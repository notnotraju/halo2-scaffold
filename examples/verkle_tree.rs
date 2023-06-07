// We still use Poseidon, but it is
// more of a fig leaf.
mod ipa_rust_clean;

use ipa_rust_clean::{CompleteBatchIPAProof, msm,
                inner_product, hash_group_to_field,
                generate_lagrange_basis, generate_batch_evaluation_proof};

use poseidon_rust::Poseidon;
use ff::{Field, PrimeField};
use halo2_base::{

    halo2_proofs::{
        halo2curves::{
            bn256::{Fr, G1Affine, Fq},
            group::Curve, group::Group},
    },
    utils::{
    //    fs::gen_srs,
        fe_to_biguint,
    //    fe_to_bigint,
        biguint_to_fe, ScalarField,
    //    bigint_to_fe,
    }
};

use num_traits::pow;
use serde::{Deserialize, Serialize};
use snark_verifier::util::arithmetic::PrimeCurveAffine;

// write something to generate single VerkleTree proof.

const LEN: usize = 32;
const HALF_LEN: usize = 16;
const WIDTH: usize = 256;
const LOG_WIDTH: usize = 8;

type VecByteArrays = Vec<Vec<u8>>;
pub struct SingleVerkleProof{
    pub commitment: G1Affine,
    pub key: Vec<u8>,
    pub path: VecByteArrays, // path: a vector of byte arrays whose concatenation is key.
                            // <byte_array_0, ...>. Q: what happens to suffix v stem?
                            // think about on June 7.
                            // byte_array_0[0] will represent first branch from root.
                            // what about last? byte_array_last could be just the suffix?
                            // either way, the first byte of byte_array_last will tell me
                            // branching from an internal node.
    pub value: Vec<u8>,
    pub proof: CompleteBatchIPAProof,
}

pub struct BatchVerkleProof{
    pub commitment: Vec<G1Affine>,
    pub keys: Vec<Vec<u8>>,
    pub paths: Vec<VecByteArrays>,}

pub struct SuffixExtensionNode{
    pub stem: Vec<u8>,
    pub suffix_commitments: (G1Affine, G1Affine), //(C1, C2), commitments to the modified leaves 
    pub extension_commitment: G1Affine, // C = Commit (1, stem, C1, C2, 0,...,0)
    pub left_leaves: Vec<Fr>,
    pub right_leaves: Vec<Fr>,
}
pub struct InternalNode{
    pub children_commitments: Vec<G1Affine>, // (C_0,..., C_{255}). need to set ``default values''!
    pub commitment: G1Affine,
    pub truncated_key: Vec<u8>,
}
// here we describe our vector commitment scheme
// note that we have transformed to lagrange basis.
// therefore, to open at position i, we need to compute \omega^i.
pub fn commit_vector(to_commit: Vec<Fr>,
                    lagrange_bases: Vec<Vec<Fr>>,
                    g_init: Vec<G1Affine>)->G1Affine{
    let coefficients_to_add = to_commit.iter()
                                .zip(lagrange_bases.iter())
                                .map(|(x, y)| 
                                {y.iter().map(|z| x * z).collect::<Vec<_>>()})
                                .collect::<Vec<_>>();
    let coefficients = coefficients_to_add.iter()
                        .fold(vec![Fr::zero(); 256], |acc, x| 
                        {acc.iter().zip(x.iter()).map(|(a, b)| a + b).collect::<Vec<_>>()});
    msm(&g_init, &coefficients)
}

pub fn commit_vector_group(to_commit: Vec<G1Affine>, lagrange_bases: Vec<Vec<Fr>>, g_init: Vec<G1Affine>)->G1Affine{
    let to_commit = to_commit.iter().map(|x| hash_group_to_field(poseidon_hash_g1(*x))).collect::<Vec<_>>();
    commit_vector(to_commit, lagrange_bases, g_init)
}

pub fn pow_of_r(r: u64, k: usize)->Vec<Fr>{
    let mut pow_of_r = vec![Fr::one()];
    let mut current_power = Fr::one();
    for _ in 1..k{
        current_power *= Fr::from(r);
        pow_of_r.push(current_power);
    }
    pow_of_r
}
pub fn rev_pow_of_r(r: u64, k: usize)->Vec<Fr>{
    let mut answer = pow_of_r(r, k);
    answer.reverse();
    answer
}
pub fn value_to_verkle_form(value: &[u8])->(Fr, Fr){
    assert!(value.len() == LEN);
    let first_half = &value[0..HALF_LEN]
        .iter()
        .map(|x| Fr::from(*x as u64))
        .collect::<Vec<_>>();
    let second_half = &value[HALF_LEN..LEN]
        .iter()
        .map(|x| Fr::from(*x as u64))
        .collect::<Vec<_>>();

    let pow_of_256 = pow_of_r(256, HALF_LEN);
    // last value of curr_pow is 2^{HALF_LEN}
    let two_half_len = pow_of_256.last().unwrap() * Fr::from(256);
    
    (inner_product(first_half, &pow_of_256) + two_half_len,
    inner_product(second_half, &pow_of_256))
}

impl SuffixExtensionNode {
    pub fn new(
        g_init: Vec<G1Affine>,
        key: Vec<u8>,
        value: Vec<u8>,
        )->Self {
            assert!(key.len() == LEN);
            let stem_len = LEN - 1;
            let suffix = *key.last().unwrap();
            let stem = key[0..stem_len].to_vec();
            let stem_as_vec_fr = stem
                .iter()
                .map(|x| Fr::from(*x as u64))
                .collect::<Vec<_>>();
            let value_leaves = value_to_verkle_form(&value);
            let which_leaf_bunch = {suffix<128};
            let normalized_suffix = {
                if which_leaf_bunch {suffix as usize}
                else {(suffix - 128) as usize}
            };
            // set global constants to deal wit 256, 8, etc.
            let mut left_leaves = vec![Fr::zero();256];
            let mut right_leaves = vec![Fr::zero();256];
            let lagrange_basis = generate_lagrange_basis(8);

            if which_leaf_bunch{
                left_leaves[normalized_suffix*2] = value_leaves.0;
                left_leaves[normalized_suffix*2 + 1] = value_leaves.1;}
            else{
                right_leaves[normalized_suffix*2] = value_leaves.0;
                right_leaves[normalized_suffix*2 + 1] = value_leaves.1;
            }
            let (first_commitment, second_commitment) = 
                (commit_vector(left_leaves.clone(), lagrange_basis.clone(), g_init.clone()),
                commit_vector(right_leaves.clone(), lagrange_basis, g_init.clone()));

            let suffix_commitments = (first_commitment, second_commitment);

            // build extension node.
            let mut extension_node_vector = vec![Fr::zero(); 256];
            extension_node_vector[0] = Fr::one();

            let rev_pow_of_256 = rev_pow_of_r(256, stem_len);
            let stem_as_field_elt = inner_product(&rev_pow_of_256, &stem_as_vec_fr);

            let mut vector_to_commit_suffix = 
            vec![Fr::zero(); 256];
            vector_to_commit_suffix[0] = Fr::one();
            vector_to_commit_suffix[1] = stem_as_field_elt;
            vector_to_commit_suffix[2] = hash_group_to_field(first_commitment);
            vector_to_commit_suffix[3] = hash_group_to_field(second_commitment);

        
            let extension_commitment = msm(&g_init, &vector_to_commit_suffix);
            SuffixExtensionNode{
                stem,
                suffix_commitments,
                left_leaves,
                right_leaves,
                extension_commitment,
            }
        }
}


impl InternalNode{
    pub fn build_nodes_from_path(
        g_init: Vec<G1Affine>,
        key: Vec<u8>,
        path: Vec<Vec<u8>>,
        value: Vec<u8>
    )->(Vec<Self>, SuffixExtensionNode){
        // build a list of the "truncated paths" from the path. This is the set of iterated concatenations.

        let mut truncated_paths = vec![];
        let mut last_full_path = vec![];
        for chunk in path.iter(){
            last_full_path.extend(chunk.clone());
            truncated_paths.push(chunk.clone());
        }
        // build the SuffixExtensionNode
        let suffix_extension_node =
             SuffixExtensionNode::new(g_init.clone(), key.clone(), value.clone());
        // first child commitment is the extension_commitment.
        let mut child_commitment = suffix_extension_node.extension_commitment;
        let stem_len = LEN - 1;
        let stem = key[0..stem_len].to_vec();
        let branching_bytes = path.iter().map(|x| x[0]).collect::<Vec<u8>>();
        let path_len = path.len();
        let internal_nodes: Vec<InternalNode> = vec![];

        // is this path_len or path_len-1??
        // as of June 7: path_len
        for i in (0..path_len).rev(){
            let branching_byte = branching_bytes[i];
            let mut children_commitments = vec![G1Affine::identity(); 256];
            children_commitments[branching_byte as usize] = child_commitment;
            
            let internal_node = InternalNode{
                children_commitments,
                commitment: G1Affine::identity(),
                truncated_key: last_full_path.clone(),
            };


        }
        //TODO: there is an ambiguity of what path is. We should work this out carefully.

        unimplemented!();
    }

}
impl SingleVerkleProof{
    pub fn new(
        g_init: Vec<G1Affine>,
        key: Vec<u8>,
        path: Vec<Vec<u8>>,
        value: Vec<u8>
    ) -> Self{

        assert!(key.len() == LEN && value.len() == LEN);
        let first_half_value = &value[0..HALF_LEN];
        let second_half_value = &value[HALF_LEN..32];

        let mut key_from_path = Vec::new();
        for byte_array in &path {
            key_from_path.extend(byte_array.clone());
        }
        // force key == concatenation of path (for testing)
        assert_eq!(key, key_from_path);
        let branching_bytes = path.iter().map(|x| x[0]).collect::<Vec<u8>>();

        // the suffix extension claims.
        let suffix = *branching_bytes.last().unwrap();
        let stem_len = HALF_LEN - 1;
        let stem_as_vec_fr = (0..stem_len)
            .map(|i| Fr::from((key[i] as u64)))
            .collect::<Vec<_>>();
        let stem_as_bytes = &key[0..stem_len];
        // value_leaves = the two values that are the leaves of the suffix extension,
        // i.e., the way the verkle tree "stores" the value in *two* leaves (rather than one)
        // (it needs two because the field is only 254 bits.)
        let value_leaves = value_to_verkle_form(&value);
        
        let which_leaf_bunch = {if suffix<128 {true} else {false}};

        let normalized_suffix = {
            if which_leaf_bunch {suffix as usize}
            else {(suffix - 128) as usize}
        };

        let mut first_leaf_bunch = vec![Fr::zero();256];
        let mut second_leaf_bunch = vec![Fr::zero();256];
        let mut first_commitment = G1Affine::identity();
        let mut second_commitment = G1Affine::identity();
        if which_leaf_bunch{
            first_leaf_bunch[normalized_suffix*2] = value_leaves.0;
            first_leaf_bunch[normalized_suffix*2 + 1] = value_leaves.1;
            first_commitment = msm(&g_init, &first_leaf_bunch);}
        else{
            second_leaf_bunch[normalized_suffix*2] = value_leaves.0;
            second_leaf_bunch[normalized_suffix*2 + 1] = value_leaves.1;
            second_commitment = msm(&g_init, &second_leaf_bunch);
        }
        let mut extension_node_vector = vec![Fr::zero(); 256];
        extension_node_vector[0] = Fr::one();

        let mut rev_pow_of_256 = vec![Fr::one(), Fr::from(256)];
        for _ in 2..stem_len{
            rev_pow_of_256.push(rev_pow_of_256.last().unwrap() * Fr::from(256));
        }
        rev_pow_of_256.reverse();
        let stem_as_field_elt = inner_product(&rev_pow_of_256, &stem_as_vec_fr);

        let mut vector_to_commit_suffix = 
            vec![Fr::zero(); 256];
        vector_to_commit_suffix[0] = Fr::one();
        vector_to_commit_suffix[1] = stem_as_field_elt;
        vector_to_commit_suffix[2] = hash_group_to_field(first_commitment);
        vector_to_commit_suffix[3] = hash_group_to_field(second_commitment);

        
        let suffix_commit = msm(&g_init, &vector_to_commit_suffix);
              
        let path_len = path.len();

        

        unimplemented!()
    }

}

#[test]
fn test_value(){
    let value = vec![1; 32];
    let verkle_form = value_to_verkle_form(&value);
    println!("verkle_form: {:?}", verkle_form);
}
fn main(){
    println!("Hello, world!");
}
