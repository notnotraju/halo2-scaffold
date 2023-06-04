// We still use Poseidon, but it is
// more of a fig leaf.

use poseidon_rust::Poseidon;
use ff::{Field, PrimeField};
use halo2_base::{

    halo2_proofs::{
        halo2curves::{
            bn256::{Fr, G1Affine, Fq},
            group::Curve},
    },
    utils::{
    //    fs::gen_srs,
        fe_to_biguint,
    //    fe_to_bigint,
        biguint_to_fe,
    //    bigint_to_fe,
    }
};

use num_traits::pow;

// use rand::thread_rng;
// use halo2_proofs::halo2curves::CurveAffine;

// use rand::{rngs::OsRng, thread_rng};
use serde::{Deserialize, Serialize};
// use std::{
//     fs::{self, File},
//     io::{BufRead, BufReader},
// };


// order is 2^{28}
pub fn compute_2_k_root(k: usize, log_order: usize) -> Fr {
    let base = Fr::root_of_unity();
    let mut answer = base;
    let goal_order = log_order - k;
    for _ in 0..goal_order {
        answer = answer.square();
    }
    answer
}
#[test]
fn test_2_k_root(){
    let test_answer = compute_2_k_root(2, 28);
    assert_eq!(test_answer.square().square(), Fr::one());
}
// compute a "lagrange basis" for 2^k roots of unity.
// we assume here that k<=10.
// more precisely, set n=2^k and \omega a primitive nth root of unity.
// then P_i is the degree n polynomial that is 1 at \omega^i and
// 0 at the other nth roots of unity.

// we use the formula (derived from Feist's notes):
// P_i = 1/2^k * [1=omega^{2^k}, \omega^{2^k-i},...,\omega^i]
// specialized for F_r, based on the fact that 2^28 is the
// power of 2 dividing r-1.
pub fn langrange_basis(k: usize)->Vec<Vec<Fr>> {
    assert!(k<=10);
    let mut lagrange_basis: Vec<Vec<Fr>> = Vec::new();
    let omega = compute_2_k_root(k, 28);
    let omega_inv = omega.invert().unwrap();
    let two_k_usize = 2usize.pow(k as u32);
    let two_k = Fr::from(two_k_usize as u64);
    // powers_of_omega = [1, omega, omega^2, ...,\omega^{2^k-1}}]
    let mut powers_of_omega: Vec<Fr> = Vec::new();
    {
        let mut current_power_of_omega = Fr::one();
        for i in 0..two_k_usize {
            powers_of_omega.push(current_power_of_omega);
            current_power_of_omega *= omega;
        }
    }
    let powers_of_omega_inv: Vec<Fr> = powers_of_omega.iter().map(|x| x.invert().unwrap()).collect();
    // denominator as a field element.
    let two_k_inv = Fr::from(two_k_usize as u64).invert().unwrap();
    // the formula is 1/2^k * [1, \omega^{-i}, ...], where
    // here, the jth entry corresponds to the coefficient of X^j of the polynomial.
    for i in 0..two_k_usize {
        let lagrange_poly = (0..two_k_usize)
            .map(|j|
                powers_of_omega_inv[i*j % two_k_usize]
                * two_k_inv)
            .collect::<Vec<_>>();
        // println!("The value at omega^3 is {:?}", lagrange_poly.iter().zip(powers_of_omega.iter().map(|x| x.square()*x)).map(|(x, y)| x*y).fold(Fr::zero(), |acc, x| acc+x));
        lagrange_basis.push(lagrange_poly);
        
    }
    lagrange_basis
}

// "hash" a group element to a (scalar) field element.
// we convert x and y to bigUints, add them, and then reduce mod r.
// not collision resistent, but good enough for prototyping.
pub fn hash_group_to_field(p: G1Affine)->Fr{
    let (x, y) = (p.x, p.y);
    let (x, y) = (fe_to_biguint(&x), fe_to_biguint(&y));
    let (x, y): (Fr, Fr) = (biguint_to_fe(&x), biguint_to_fe(&y));
    x+y
}

#[test]
fn test_hash_group(){
    let g = G1Affine::random(&mut rand::thread_rng());
    let h = G1Affine::generator();
    let h: G1Affine = (h+h).into();
    println!("The random element g is {:?}", g);
    let output = hash_group_to_field(g);
    println!("The hash of the random element is {:?}", output);
}
// inputs: a vector of even length of field elements and a scalar w
// computes vector_{lo} * w + vector{hi}* w^{-1}
// folding of a will be fold(a, w). folding of b will be fold(b, w^{-1})
pub fn fold_vector_scalars<F: PrimeField>(vector: &Vec<F>, w: &F) -> Vec<F> {
    let mut folded_vector: Vec<F> = Vec::new();
    let w_inv = w.invert().unwrap();
    let l = vector.len();
    assert!(l%2 == 0); // make sure length is even
    for i in 0..l/2 {
        folded_vector.push(vector[i]*w + vector[i+l/2]* w_inv);
    }
    folded_vector
}

// inputs: a vector of even length of group elements, and a scalar w
// outputs vector_lo * w + vector_hi* w^{-1}
pub fn fold_vector_group(vector: &Vec<G1Affine>, w: &Fr) -> Vec<G1Affine> {
    let mut folded_vector: Vec<G1Affine> = Vec::new();
    let w_inv = w.invert().unwrap();
    let l = vector.len();
    assert!(l%2 == 0); // make sure length is even
    for i in 0..l/2 {
        folded_vector.push((vector[i]* *w + vector[i+l/2]* w_inv).to_affine());
    }
    folded_vector
}

// standard msm
pub fn msm(vec_g: &[G1Affine], vec_a: &[Fr]) -> G1Affine {
    let msm_answer = vec_g
        .iter()
        .zip(vec_a.iter())
        .map(|(g, a)| g * a)
        .reduce(|a, b| a + b)
        .unwrap()
        .to_affine();
    msm_answer
}
// standard inner product
pub fn inner_product(vec_a: &[Fr], vec_b: &[Fr]) -> Fr {
    let inner_product = vec_a
        .iter()
        .zip(vec_b.iter())
        .map(|(a, b)| a * b)
        .reduce(|a, b| a + b)
        .unwrap();
    inner_product
}

// prover util
// compute L and R from vec_a, vec_g, vec_b, and u.
pub fn compute_l_r(vec_a: &Vec<Fr>, vec_g: &Vec<G1Affine>,
                    vec_b: &Vec<Fr>, u: &G1Affine) 
                            -> (G1Affine, G1Affine) {
    let l = vec_a.len();
    assert!(vec_a.len() == vec_g.len() && 
        vec_a.len() == vec_b.len());
    assert!(l%2 == 0); // make sure length is even
    // L = <a_{step,lo}, g_{step, hi}> + <a_{step,lo}, b_{step,hi}>u
    // R = <a_{step,hi}, g_{step, lo}> + <a_{step,hi}, b_{step,lo}>u
    let left = msm(
        &vec_g[l/2..], &vec_a[..l/2]) + 
        u * inner_product(&vec_a[..l/2], &vec_b[l/2..]
    );
    let right = msm(
        &vec_g[..l/2], &vec_a[l/2..]) + 
        u * inner_product(&vec_a[l/2..], &vec_b[..l/2]
    );
//    println!("At the current stage, (L,R) are ({:?}, {:?})", L, R);
    (left.into(), right.into())
}

// binary counting pattern: given
// w_1,..., w_k, computing the following list of size 2^k:
// \prod(w_i)^{-1}, ..., \prod(w_i), where the bit flips according
// to binary counting. this is a verifier util.
pub fn binary_counting_pattern(vec_w: &Vec<Fr>)-> Vec<Fr> {
    let mut pattern: Vec<Fr> = Vec::new();
    let mut w_pos_prod = Fr::one();
    for w in vec_w.iter(){
        w_pos_prod *= w;
    }
    let w_init = w_pos_prod.invert().unwrap();
    pattern.push(w_init);
    for i in 1..(1<<vec_w.len()){
        let mut w_prod = w_init;
        for j in 0..vec_w.len(){
            if i & (1<<j) != 0 {
                w_prod *= vec_w[j]* vec_w[j];
            }
        }
        pattern.push(w_prod);
    }
    pattern
}

// reverse binary counting pattern.
pub fn binary_counting_pattern_reverse(vec_w_rev: &Vec<Fr>)->Vec<Fr>{
    let mut w_vec = vec_w_rev.clone();
    w_vec.reverse();
    binary_counting_pattern(&w_vec)
}


// power of 2 functions.
pub fn check_power_of_two(n: usize) -> bool {
    n != 0 && (n & (n - 1)) == 0
}
pub fn int_log_2(n: usize)-> usize{
    assert!(check_power_of_two(n));
    let mut log = 0;
    let mut n = n;
    while n > 1 {
        n >>= 1;
        log += 1;
    }
    log
}

// build vector functions.

// given a usize n, return a vector of length l
// where the n-th element is 1 and the rest are 0.
pub fn usize_to_unit_vec(n: usize, l: usize)->Vec<Fr> {
    assert!(n < l);
    // compute the vector and return it.
    (0..l).map(|i|{
        if i == n {
            Fr::one()
        } else {
            Fr::zero()
        }
    }).collect::<Vec<Fr>>()   
}

// given z and n, build the vector (1,z,...,z^{n-1})
pub fn build_poly_vector(z: &Fr, n: usize)->Vec<Fr>{
    let mut poly_vec: Vec<Fr> = Vec::new();
    let mut z_pow = Fr::one();
    for _ in 0..n {
        poly_vec.push(z_pow);
        z_pow *= z;
    }
    poly_vec
}

// given a u64, return the binary expansion as a vector length l.
// note: no bound checking.
pub fn u64_to_bin_vec(n: u64, l: u64)->Vec<Fr>{
    let mut bin: Vec<Fr> = Vec::new();
    let mut n = n;
    for _ in 0..l {
        bin.push(Fr::from(n & 1));
        n >>= 1;
    }
    bin.reverse();
    bin
}


// compute b_0 given z and the stage_randomness (w_k, ..., w_1).
// algorithm: b_0 = prod(w_j^{-1}+ w_jz^{2^{j-1}})
// where w_j is the *k-j*th element of stage_randomness.
// this product goes from j=1 to j=k?

// TODO: rename? The reason is that this pattern comes up at other
// in the code.
pub fn compute_b_fin_poly(z: &Fr, stage_randomness: &[Fr])-> Fr{
    let k = stage_randomness.len();
    let mut two_primary_powers_of_z = vec![*z];
    for i in 1..k{
        two_primary_powers_of_z.push(
            two_primary_powers_of_z[i-1]*two_primary_powers_of_z[i-1]);
    }
    two_primary_powers_of_z.reverse();
    
    let b_0 = stage_randomness.iter()
        .zip(two_primary_powers_of_z.iter())
        .map(|(w, z_pow)|  w.invert().unwrap() + w*z_pow)
        .fold(Fr::one(), |acc, x| acc*x);
    b_0
}


// a struct containing the proof of inclusion.
// stage proof is in order: stage k, stage k-1, ..., stage 1.
// final_a is the final a value.
// note that we do not need any final_b, because b is assumed 
// to be known, hence the verifier can simply compute b herself.
// BatchingHelperInfo contains the claimed stage_randomness
// as well as the claimed g_0. This is useful when we batch proofs.

// the model here is that the other inputs needed for the proof,
// namely g_init, z, and revealed evaluation, are all
// assumed to be public.
#[derive(Debug, Clone, Deserialize)]
pub struct ProofOfInclusion {
//    pub random_field_element: Fr,
    pub revealed_evaluation: Fr, // element claimed to be revealed
    pub stage_proof: Vec<[G1Affine; 2]>,
    pub final_a: Fr,
    pub batching_helper_info: Option<BatchingHelperInfo>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct BatchingHelperInfo{
    pub stage_randomness: Vec<Fr>,
    pub g_0: G1Affine,
}
#[derive(Debug, Clone, Deserialize)]
pub struct BatchProofOfInclusion{
    pub list_of_proofs: Vec<ProofOfInclusion>,
    pub commitment_to_weighted_poly: G1Affine,
    pub proof_of_weighted_poly: ProofOfInclusion
}
// contains all of the information we need for the verifier to
// verify a single IPA proof.
#[derive(Debug, Clone, Deserialize)]
pub struct CompleteSingleIPAProof{
    pub commitment: G1Affine,
    pub z: Fr,
    pub proof: ProofOfInclusion,
    pub g_init: Vec<G1Affine>,
    pub u: G1Affine,
}
// all the information I need for batch verification.

#[derive(Debug, Clone, Deserialize)]
pub struct CompleteBatchIPAProof {
    pub commitments: Vec<G1Affine>,
    pub vec_z: Vec<Fr>,
    pub batch_proof: BatchProofOfInclusion,
    pub g_init: Vec<G1Affine>, // g_init is the same for all batched proofs.
    pub u: G1Affine
}

// a generic function to generate hasher so that we can 
// easily synchronize behavior for prover and verifier.
// NOTE: we put this on the backburner at the moment, as 
// it is not compatible with PoseidonChip.
pub fn generate_hasher()->Poseidon<Fr, 3, 2>{
    let number_of_full_rounds = 8;
    let number_of_half_rounds = 33;
    Poseidon::<Fr, 3, 2>::new(number_of_full_rounds, number_of_half_rounds)
}

// compute_randomness is a verifier util.
// given a ProofOfInclusion, compute the vector stage_randomness.
// this is simulating the Fiat-Shamir process, and outputs
// a vector <w_k, ..., w_1>, where the numbering refers to 
// the stage to which it corresponds. (see blog post or halo paper)

// here, we have a use_poseidon flag, which is used to determine
// if we use the Poseidon hash function as well. (As of now, we don't.)
pub fn compute_randomness(
    proof: &ProofOfInclusion,
    use_poseidon: bool) -> Vec<Fr> {
        let mut stage_randomness = Vec::new();
        let revealed_element = proof.revealed_evaluation;
        let stage_proof = &proof.stage_proof;
        if use_poseidon {
            let mut hasher = generate_hasher();
            hasher.update(&[revealed_element]); 
            for _stage in stage_proof.iter(){
                // this is the key step, where we use the stage proof.
                // in subsequent iterations, this will be improved!
                // hasher.update(&[hash_group_to_field(stage[0]), hash_group_to_field(stage[1])]);
                stage_randomness.push(hasher.squeeze());
            }
        }
        else {
            // if the use_poseidon flag is false,
            // we set stage_randomness[0] = revealed_element
            // and stage_randomness[i] = 
            // stage_randomness[i-1]*revealed_element +
            // hash(current_stage[0]) + hash(current_stage[1])
            for stage in stage_proof.iter(){
                match stage_randomness.last() {
                    Some(last_element) => {
                        stage_randomness.push(
                            last_element*revealed_element
                        +   hash_group_to_field(stage[0])
                        +   hash_group_to_field(stage[1]));
                    },
                    None => {
                        stage_randomness.push(revealed_element);
                    }
                }
            }
        }
        stage_randomness
    }

// a simple protocol to ``batch randomness''. We compute two "random elements":
// the first is the product of the last elements of each stage_randomness vector
// the second is the square of the first.
// TODO: improve to a better hash function (once I get compatibility with e.g. Poseidon)
pub fn compute_batching_randomness(proofs_of_inclusion: &[ProofOfInclusion])->[Fr; 2] {
    let first_randomness = 
        proofs_of_inclusion.iter()
        .map(|proof|
            if let Some(batching_helper_info) = &proof.batching_helper_info {
                batching_helper_info.stage_randomness.last().unwrap()
            }
            else {
                panic!("batching_helper_info is not present!");
            }
            )
        .fold(Fr::one(), |acc, x| acc*x);
    let second_randomness = first_randomness.square();
    [first_randomness, second_randomness]
}

// generate a single evaluation proof, (i.e., IPA as PCS).
// note that vector_to_commit is the vector of coefficients of the polynomial.
// improve later!
pub fn generate_single_evaluation_proof(
    g_init: &Vec<G1Affine>,
    u: &G1Affine,
    vector_to_commit: &Vec<Fr>,
    z: &Fr,
    batching: bool) -> ProofOfInclusion {
    // n is the length of the vector to be commited.
    let n = g_init.len();
    assert!(check_power_of_two(n) && n == vector_to_commit.len());
    let k = int_log_2(n);
    // set up pederson commit, and the running vectors storing
    // the current a, g, b values.
    let _pederson_commit = msm(g_init, vector_to_commit);

    let mut a_vec = Vec::new();
    let mut g_vec = Vec::new();
    let mut b_vec = Vec::new();

    let mut a_current = vector_to_commit.clone();
    let mut g_current = g_init.clone();
    let mut b_current = build_poly_vector(&z, n);

    // claimed evaluation
    let evaluation = inner_product(vector_to_commit, &b_current);

    let mut current_hash:Fr; // set current_hash to a default value, destroying rust norms.
    // for the purposes of this iteration (to avoid use of PoseidonChip)
    // I set the initial value of current_hash to 1.
    // In the loop, the actual first pushed value will be evaluation.
    current_hash = Fr::one();
    // build the hasher
    let mut hasher = generate_hasher();
    
    // in this code, I will not use this.
    // put the claimed evaluation into the hasher.
    hasher.update(&[evaluation]); // revealed claimed evaluation.

    a_vec.push(a_current.clone());
    g_vec.push(g_current.clone());
    b_vec.push(b_current.clone());

    let mut left: Vec<G1Affine> = Vec::new();
    let mut right: Vec<G1Affine> = Vec::new();
    let mut stage_randomness: Vec<Fr> = Vec::new();

    // goes from step k to step 1. These are the stages
    // with numbering taken from the halo paper.
    for step in (1..k+1).rev() {

        let (left_step, right_step) = compute_l_r(
        &a_current,
        &g_current,
        &b_current, 
            u);

        left.push(left_step);
        right.push(right_step);
        // current_hash is my surrogate Fiat-Shamir.
        // this will be improved later.
        current_hash *= evaluation;
        // so, first stage_randomness is evaluation. after that, I take
        // current_hash = (current_hash*evaluation)+hash(L_step) + hash(R_step)
        
        if step!=k {current_hash += hash_group_to_field(left_step)
                        + hash_group_to_field(right_step);}
        stage_randomness.push(current_hash);
        let current_hash_inv = current_hash.clone().invert().unwrap();
        // fold the vectors a, b, g
        (a_current, g_current, b_current) =
        (fold_vector_scalars(&a_current, &current_hash),
        fold_vector_group(&g_current, &current_hash_inv),
        fold_vector_scalars(&b_current, &current_hash_inv));
        // push the new a, b, and g to state.
        a_vec.push(a_current.clone());
        g_vec.push(g_current.clone());
        b_vec.push(b_current.clone());
    }
    // compute the final a value.
    let final_a = a_current[0];
    let g_0 = g_current[0];
    
    // here, stage_proofs is a vector of size k. The lth element is the *stage k-l* proof.
    // In particular: [[L_k, R_k], [L_{k-1}, R_{k-1}], ..., [L_1, R_1]]
    // I emphasize: we are using the numbering from the Halo paper!
    let stage_proof = left.iter()
                .zip(right.iter())
                .map(|(l_step, r_step)| [*l_step, *r_step])
                .collect::<Vec<[G1Affine;2]>>();
    
    let batching_helper_info = {
    if batching {
        Some(
            BatchingHelperInfo{
                g_0,
                stage_randomness
            })
    }
    else {None}
    };
    ProofOfInclusion{
        revealed_evaluation: evaluation,
        stage_proof,
        final_a,
        batching_helper_info}
}

pub fn generate_batch_evaluation_proof(
    g_init: &Vec<G1Affine>,
    u: &G1Affine,
    vectors_to_commit: &Vec<Vec<Fr>>,
    vec_z: &Vec<Fr>,
)-> BatchProofOfInclusion{

    assert!(vec_z.len() == vectors_to_commit.len());
    let n = g_init.len();
    let _commitments = vectors_to_commit.iter()
        .map(|vector_to_commit| msm(g_init, vector_to_commit))
        .collect::<Vec<_>>();
    
    // list_of_proofs is a list of the inclusion proofs.
    // note that this will also contain the extra information
    // in batching_helper_info.
    let list_of_proofs = 
        vectors_to_commit.iter()
        .zip(vec_z.iter())
        .map(|(vector_to_commit, z)| generate_single_evaluation_proof(g_init, u, vector_to_commit, z, true))
        .collect::<Vec<_>>();

    // t is the point at which we evaluate the "r-weighted polynomial"
    // For every proof \pi_i, let P_i be the "binary counting polynomial", based on the corresponding
    // stage_randomness. This is computed by the function ##compute_b_fin_poly##
    // Then the r-weighted polynomial is \sum r^i P_i.
    let [r, t] = compute_batching_randomness(&list_of_proofs);
    // per usual, we "reduce" the problem to a single polynomial evaluation
    // proof, for the following "batched" polynomial: \sum r^i P_i.
    // How do I compute P_i? It is just a vector given
    // by binary_counting_pattern_reverse of stage_randomness_i.
    let mut weighted_polynomials: Vec<Vec<Fr>> = Vec::new();
    let mut sum_of_weighted_polynomials: Vec<Fr> = vec![Fr::zero(); n];
    // power_of_r starts at 1, and is incremented by r at each step
    // in the for loop.
    let mut power_of_r = Fr::one();
    for proof in list_of_proofs.clone() {
        let stage_randomness = proof.batching_helper_info
                                        .unwrap().stage_randomness;
        let weighted_polynomial = 
            binary_counting_pattern_reverse(&stage_randomness)
            .iter()
            .map(|x| x * power_of_r)
            .collect::<Vec<_>>();
        sum_of_weighted_polynomials = 
            sum_of_weighted_polynomials
            .iter()
            .zip(weighted_polynomial.iter())
            .map(|(x, y)| x + y)
            .collect::<Vec<_>>();
        weighted_polynomials.push(weighted_polynomial);
        power_of_r *= r;
    }
    let commitment_to_weighted_poly = msm(g_init, &sum_of_weighted_polynomials);
    // now, we have the weighted polynomials. We need to compute the sum of these polynomials.
    // This is the batched polynomial.
    let proof_of_proofs = generate_single_evaluation_proof(g_init, u, &sum_of_weighted_polynomials, &t, false);
    BatchProofOfInclusion {
        list_of_proofs,
        commitment_to_weighted_poly,
        proof_of_weighted_poly: proof_of_proofs,
    }
}


pub fn verify_single_evaluation_proof (
    complete_single_ipa_proof: CompleteSingleIPAProof,
    ) -> bool {
    let commitment = &complete_single_ipa_proof.commitment;
    let z = &complete_single_ipa_proof.z;
    let proof = &complete_single_ipa_proof.proof;
    let g_init = &complete_single_ipa_proof.g_init;
    let u = &complete_single_ipa_proof.u;
    let n = g_init.len();
    assert!(check_power_of_two(n));
    let _k = int_log_2(n);
    
    let revealed_evaluation = &proof.revealed_evaluation;
    let stage_proofs = &proof.stage_proof;
    let final_a = &proof.final_a;

    // compute the randomness from the stage proofs.
    // the ordering of stage_randomness is the same as that of stage_proofs.
    let use_poseidon = false;
    let stage_randomness = compute_randomness(proof, use_poseidon);
    
    // compute <s,g>. this means I need to use the binary counting pattern!
    // technical point: here I need to reverse the usual binary_counting_pattern.
    // note that this is the only essentially linear time part of the algorithm.
    let g_0 = msm(g_init, &binary_counting_pattern_reverse(&stage_randomness));
    // compute b_0 
    let b_0 = compute_b_fin_poly(z, &stage_randomness);
    // println!("b_0: {:?}", b_0);
    let mut left: Vec<G1Affine> = Vec::new();
    let mut right: Vec<G1Affine> = Vec::new();
    stage_proofs.iter().for_each(|[l_step, r_step]|{
    left.push(*l_step);
    right.push(*r_step);
    });

    // left and right are in order k..1 (same as stage_proofs).
    let w_squared = stage_randomness.iter()
                .map(|r| r.square())
                .collect::<Vec<Fr>>();
    let w_inv_squared = stage_randomness.iter()
        .map(|r| r.square().invert().unwrap())
        .collect::<Vec<Fr>>();
    let p_prime = commitment + u*revealed_evaluation;
    let first_q = msm(&left, &w_squared)
     + msm(&right, &w_inv_squared)
     + p_prime;
     //println!("Rust computes first_q as {:?}", first_q.to_affine());
    //  println!("folded L is {:?}", msm(&L, &w_squared));
    // println!("folded R is {:?}", msm(&R, &w_inv_squared));
    // println!("Rust verifier computes u*b_0 as {:?}", (u*b_0).to_affine());
    // println!("Rust verifier computes g_0+u*b_0 as {:?}", (g_0 + u*b_0).to_affine());
    let second_q = (g_0 + u*b_0)*final_a;
    // println!("first_q, is {:?}", first_q.to_affine());
    // println!("second_q is {:?}", second_q.to_affine());
    first_q == second_q
}

pub fn verify_batch_evaluation_proof(
    batched_ipa_proof: &CompleteBatchIPAProof,
)-> bool {
    let commitments = &batched_ipa_proof.commitments;
    let vec_z = &batched_ipa_proof.vec_z;
    let batch_proof = &batched_ipa_proof.batch_proof;
    let g_init = &batched_ipa_proof.g_init;
    let u = &batched_ipa_proof.u;

    let list_of_proofs = &batch_proof.list_of_proofs;
    let commitment_to_weighted_poly = &batch_proof.commitment_to_weighted_poly;
    let proof_of_weighted_poly = &batch_proof.proof_of_weighted_poly;

    let n = g_init.len(); // is this true??
    let m = commitments.len();
    // compute r and t.
    // steps: compute the w_i from each proof.
    
    // compute the claimed evaluation of the r-weighted polynomial at t.
    // check the proof of this claimed evaluation
    let [r, t] = compute_batching_randomness(list_of_proofs);

    // list_stage_randomness is a vector consisting of the "stage_randomness"
    // from every proof, i.e., a vector of the form (w_k,...,w_1) for every proof.
    // note that, although in my implementation this is provided by the prover,
    // we compute it oursevles in the verification -- we simply compute it.
    let list_stage_randomness = list_of_proofs.iter()
        .map(|proof| compute_randomness(proof, false))
        .collect::<Vec<_>>();
    let powers_of_r = build_poly_vector(&r, m);
    // change name of compute_b_fin_poly, to reflect what is actually happening.
    let claimed_evaluation = list_stage_randomness.iter()
        .zip(powers_of_r.iter())
        .map(|(stage_randomness, pow_of_r)| 
            pow_of_r * compute_b_fin_poly(&t, stage_randomness))
        .fold(Fr::zero(), |acc, x| acc + x);
    // check that the revealed_evaluation is compatible with
    // the stage_randomness vectors and r.
    assert!(claimed_evaluation ==
        proof_of_weighted_poly.revealed_evaluation);
    
    // check single proof of evaluation.
    
    let final_evaluation_proof = CompleteSingleIPAProof{
        commitment: *commitment_to_weighted_poly,
        z: t,
        proof: proof_of_weighted_poly.clone(),
        g_init: g_init.clone(),
        u: *u,
    };
    verify_single_evaluation_proof(final_evaluation_proof)
}


#[test]
fn test_batched_ipa(){
    let batch_size = 5;
    let k = 8;
    let n = pow(2, k);
    let mut g_init = Vec::new();
    for _ in 0..n {
        g_init.push(G1Affine::random(&mut rand::thread_rng()));
    }
    let u = G1Affine::random(&mut rand::thread_rng());
    let mut vectors_to_commit: Vec<Vec<Fr>> = Vec::new();
    let mut vec_z: Vec<Fr> = Vec::new();
    // populate the vectors_to_commit and zs
    for _ in 0..batch_size {
        let vector_to_commit = (0..n).map(|_| 
            Fr::random(&mut rand::thread_rng())).collect::<Vec<Fr>>();
        vectors_to_commit.push(vector_to_commit);
        vec_z.push(Fr::random(&mut rand::thread_rng()));
    }
    let commitments = vectors_to_commit.iter()
        .map(|vector_to_commit| msm(&g_init, vector_to_commit))
        .collect::<Vec<G1Affine>>();
    let batch_proof = generate_batch_evaluation_proof(&g_init, &u, &vectors_to_commit, &vec_z);
    let final_batch_IPA_proof = CompleteBatchIPAProof{
        commitments,
        vec_z,
        batch_proof,
        g_init: g_init.clone(),
        u: u.clone(),
    };
    let did_it_work = verify_batch_evaluation_proof(&final_batch_IPA_proof);
    assert!(did_it_work);
}

#[test]
fn test_ipa() {
    let k = 8;
    let n = pow(2,k);
    let mut g_init = Vec::new();
    for _ in 0..n {
        g_init.push(G1Affine::random(&mut rand::thread_rng()));
    }
    let u = G1Affine::random(&mut rand::thread_rng());
    let vector_to_commit = (0..n).map(|_| 
            Fr::random(&mut rand::thread_rng())).collect::<Vec<Fr>>();
    // let vector_to_commit = (0..n).map(|l| 
    //         Fr::from(l)).collect::<Vec<Fr>>();
    // let vector_to_commit = vec![Fr::from(1000), Fr::from(2), Fr::one(), Fr::one()];
    let commitment = msm(&g_init, &vector_to_commit);
    println!("commitment is {:?}", commitment); 
    let z = Fr::from(1000 as u64);

    let proof = generate_single_evaluation_proof(&g_init, &u, &vector_to_commit, &z, false);
    println!("made it to proof construction");
    let complete_proof = CompleteSingleIPAProof {
        commitment,
        z,
        proof,
        g_init,
        u,
    };
    assert!(verify_single_evaluation_proof(complete_proof));
}

#[test]
fn test_b_fin_poly(){
    let z = Fr::from(2);
    let stage_randomness = vec![Fr::from(1), Fr::from(2)];
    let b_0 = compute_b_fin_poly(&z, &stage_randomness);
    let mut poly = build_poly_vector(&z, 4);
    
    for i in 0..2 {
    
        poly = fold_vector_scalars(&poly, &stage_randomness[i].invert().unwrap());
    }
    assert_eq!(b_0, poly[0]);
}



pub fn test_ipa_export(k: usize)-> CompleteSingleIPAProof {
    let n = pow(2,k);
    let mut g_init = Vec::new();
    for _ in 0..n {
        g_init.push(G1Affine::random(&mut rand::thread_rng()));
    }
    let u = G1Affine::random(&mut rand::thread_rng());
    let vector_to_commit = (0..n).map(|_| 
            Fr::random(&mut rand::thread_rng())).collect::<Vec<Fr>>();
    // let vector_to_commit = (0..n).map(|l| 
    //         Fr::from(l)).collect::<Vec<Fr>>();
    // let vector_to_commit = vec![Fr::from(1000), Fr::from(2), Fr::one(), Fr::one()];
    let commitment = msm(&g_init, &vector_to_commit);
    let z = Fr::from(1000);
    let proof =
        generate_single_evaluation_proof(&g_init, &u, &vector_to_commit, &z, false);
    let single_proof = 
            CompleteSingleIPAProof{
            commitment,
            z,
            proof,
            g_init,
            u,
        };
    verify_single_evaluation_proof(single_proof.clone());
    single_proof
}

// what I pass to test my batch circuit verifier.
pub fn test_batch_ipa_export(k: usize, batch_size: usize)-> CompleteBatchIPAProof {

    let n = pow(2, k);
    let mut g_init = Vec::new();
    for _ in 0..n {
        g_init.push(G1Affine::random(&mut rand::thread_rng()));
    }
    let u = G1Affine::random(&mut rand::thread_rng());
    let mut vectors_to_commit: Vec<Vec<Fr>> = Vec::new();
    let mut vec_z: Vec<Fr> = Vec::new();
    // populate the vectors_to_commit and zs
    for _ in 0..batch_size {
        let vector_to_commit = (0..n).map(|_| 
            Fr::random(&mut rand::thread_rng())).collect::<Vec<Fr>>();
        vectors_to_commit.push(vector_to_commit);
        vec_z.push(Fr::random(&mut rand::thread_rng()));
    }
    let commitments = vectors_to_commit.iter()
        .map(|vector_to_commit| msm(&g_init, vector_to_commit))
        .collect::<Vec<G1Affine>>();
    let batch_proof = generate_batch_evaluation_proof(&g_init, &u, &vectors_to_commit, &vec_z);
    CompleteBatchIPAProof{
        commitments,
        vec_z,
        batch_proof,
        g_init: g_init.clone(),
        u,
    }
}

// test 2-primary root of unity stuff.
// seems that root_of_unity() has order 2^{28}
// to compute lagrange basis for 2^n, we need the "barycentric formula"
#[test]
fn compute_2_primary_root_of_unity(){
    let base = Fr::root_of_unity();
    let mut i=0;
    let mut power = base;
    while power != Fr::one() {
        power = power.square();
        i+=1;
    }
    println!("i is {}", i);
}
#[test]
fn test_binary_counting(){
    let test_input = vec![Fr::from(1), Fr::from(2)];
    let output = binary_counting_pattern(&test_input);
   println!("The output is: {:?}", output);
   println!("For reference, the inverse of 2 is: {:?}", Fr::from(2).invert().unwrap());
}
#[test]
fn test_lagrange_basis(){
    let k = 2;
    let lagrange_basis = langrange_basis(k);
    println!("The lagrange basis is: {:?}", lagrange_basis);

}
fn main(){
    println!("Hello, world!");
}
