// We still use Poseidon, but it is
// more of a fig leaf.
mod ipa_rust_clean;

use ipa_rust_clean::{CompleteBatchIPAProof, msm, inner_product, hash_group_to_field};

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

type path: Vec<Vec<u8>>;

use snark_verifier::util::arithmetic::PrimeCurveAffine;

// DEFAULT ASSUMPTION: 32 bytes for key, 32 bytes for value.
// write something to generate single VerkleTree proof.

const LEN: usize = 32;
const HALF_LEN: usize = 16;

type VecByteArrays = Vec<Vec<u8>>;
pub struct SingleVerkleProof{
    pub commitment: G1Affine,
    pub key: Vec<u8>,
    pub path: VecByteArrays,
    pub value: u8,
    pub proof: CompleteBatchIPAProof,
}

pub struct BatchVerkleProof{
    pub commitment: Vec<G1Affine>,
    pub keys: Vec<Vec<u8>>,
    pub paths: Vec<path>,}

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

    let mut pow_of_256: Vec<Fr> = vec![Fr::one(), Fr::from(256)];
    let mut curr_pow = Fr::from(256);
    for _ in 2..HALF_LEN{
        curr_pow *= Fr::from(256);
        pow_of_256.push(curr_pow);
    }
    // last value of curr_pow is 2^{HALF_LEN}
    let two_half_len = curr_pow * Fr::from(256);
    
    (inner_product(first_half, &pow_of_256) + two_half_len,
    inner_product(second_half, &pow_of_256))
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
