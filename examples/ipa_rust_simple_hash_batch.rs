// We still use Poseidon, but it is
// more of a fig leaf.


use std::sync::Arc;

use ark_std::{start_timer, end_timer};
//use halo2::arithmetic::Curve;
use poseidon_rust::Poseidon;
// use halo2::primitives/poseidon::{Poseidon, PoseidonParameters};
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
use rand::thread_rng;
// use halo2_proofs::halo2curves::CurveAffine;
use num_traits::pow;
// use rand::{rngs::OsRng, thread_rng};
// use serde::{Deserialize, Serialize};
// use std::{
//     fs::{self, File},
//     io::{BufRead, BufReader},
// };

// this file is better than ipa_rust_old in that it uses
// Poseidon to do the FS transform.


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

// computes, vector_lo * w + vector_hi* w^{-1}
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

// standard MSM
pub fn MSM(vec_g: &Vec<G1Affine>, vec_a: &Vec<Fr>) -> G1Affine {
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

// compute L and R from vec_a, vec_g, vec_b, and U.
// this is a prover util.
pub fn compute_L_R(vec_a: &Vec<Fr>, vec_g: &Vec<G1Affine>,
                    vec_b: &Vec<Fr>, U: &G1Affine) 
                            -> (G1Affine, G1Affine) {
    let l = vec_a.len();
    assert!(vec_a.len() == vec_g.len() && 
        vec_a.len() == vec_b.len());
    assert!(l%2 == 0); // make sure length is even
    // L = <a_{step,lo}, g_{step, hi}> + <a_{step,lo}, b_{step,hi}>U
    // R = <a_{step,hi}, g_{step, lo}> + <a_{step,hi}, b_{step,lo}>U
    let L = MSM(
        &vec_g[l/2..].to_vec(), &vec_a[..l/2].to_vec()) + 
        U * inner_product(&vec_a[..l/2], &vec_b[l/2..]
    );
    let R = MSM(
        &vec_g[..l/2].to_vec(), &vec_a[l/2..].to_vec()) + 
        U * inner_product(&vec_a[l/2..], &vec_b[..l/2]
    );
//    println!("At the current stage, (L,R) are ({:?}, {:?})", L, R);
    (L.into(), R.into())
}

// binary counting pattern: given
// w_1,..., w_k, computing the following list of size 2^k:
// \prod(w_i)^{-1}, ..., \prod(w_i), where the bit flips according
// to binary counting.
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
                w_prod *= (vec_w[j]* vec_w[j]);
            }
        }
        pattern.push(w_prod);
    }
    pattern
}
// and its reverse
pub fn binary_counting_pattern_reverse(vec_w_rev: &Vec<Fr>)->Vec<Fr>{
    let mut w_vec = vec_w_rev.clone();
    w_vec.reverse();
    binary_counting_pattern(&w_vec)
}
// // idiotic hash function.
// // description: given a point g, hash(g) = x(g) + y(g)
// // where x(g) and y(g) are turned into bigints and then into F_r elements.
// // the point is to map an elliptic curve point to an element in F_r.
// // as this is passed as an *input* into Poseidon, safe. (maybe stupid.)
// pub fn hash(g: G1Affine)->Fr{
//     let sum_of_coords = fe_to_biguint(&g.x) + fe_to_biguint(&g.y);
//     let hash_output: Fr = biguint_to_fe(&sum_of_coords);
//     hash_output
// }


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

pub fn build_poly_vector(z: &Fr, n: usize)->Vec<Fr>{
    let mut poly_vec: Vec<Fr> = Vec::new();
    let mut z_pow = Fr::one();
    for _ in 0..n {
        poly_vec.push(z_pow);
        z_pow *= z;
    }
    poly_vec
}

pub fn u64_to_bin_vec(n: u64, l: u64)->Vec<Fr>{
    let mut bin: Vec<Fr> = Vec::new();
    let mut n = n;
    // while n > 0 {
    //     bin.push(Fr::from(n & 1));
    //     n >>= 1;
    // }
    for _ in 0..l {
        bin.push(Fr::from(n & 1));
        n >>= 1;
    }
    bin.reverse();
    bin
}


// compute b_0 given z and the stage_randomness (w_k, ..., w_1).
// algorithm: compute prod(w_j^{-1}+ w_jz^{2^{j-1}})
// where w_j is the k-jth element of stage_randomness.
// this product goes from ###j = 0 to j = k-1### j=1 to j=k?
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
// batching_helper_info contains the claimed stage_randomness
// as well as the claimed g_0. This is useful when we batch proofs.

// the model here is that the other inputs needed for the proof,
// namely g_init, z, and revealed evaluation, are all
// assumed to be public.
#[derive(Debug, Clone)]
pub struct proof_of_inclusion {
//    pub random_field_element: Fr,
    pub revealed_evaluation: Fr, // element claimed to be revealed
    pub stage_proof: Vec<[G1Affine; 2]>,
    pub final_a: Fr,
    pub batching_helper_info: Option<batching_helper_info>,
}

#[derive(Debug, Clone)]
pub struct batching_helper_info{
    pub stage_randomness: Vec<Fr>,
    pub g_0: G1Affine,
}
#[derive(Debug, Clone)]
pub struct batched_proof_of_inclusion{
    pub list_of_proofs: Vec<proof_of_inclusion>,
    pub commitment_to_weighted_poly: G1Affine,
    pub proof_of_weighted_poly: proof_of_inclusion
}
// contains all of the information we need for the verifier to
// verify a single IPA proof.
#[derive(Debug, Clone)]
pub struct single__IPA_proof{
    pub commitment: G1Affine,
    pub z: Fr,
    pub proof: proof_of_inclusion,
    pub g_init: Vec<G1Affine>,
    pub U: G1Affine,
}
// all the information I need for batch verification.
pub struct batch_IPA_proof {
    pub commitments: Vec<G1Affine>,
    pub vec_z: Vec<Fr>,
    pub batched_proof: batched_proof_of_inclusion,
    pub g_init: Vec<G1Affine>, // g_init is the same for all batched proofs.
    pub U: G1Affine
}

// a generic function to generate hasher so that we can 
// easily synchronize behavior for prover and verifier.
// NOTE: we put this on the backburner at the moment, as 
pub fn generate_hasher()->Poseidon<Fr, 3, 2>{
    let number_of_full_rounds = 8;
    let number_of_half_rounds = 33;
    Poseidon::<Fr, 3, 2>::new(number_of_full_rounds, number_of_half_rounds)
}

// given a proof_of_inclusion, compute the vector stage_randomness.
// here, we have a use_poseidon flag, which is used to determine
// if we are doing "stupid" randomness or poseidon.
pub fn compute_randomness(
    proof: &proof_of_inclusion,
    use_poseidon: bool) -> Vec<Fr> {
        let mut stage_randomness = Vec::new();
        let revealed_element = proof.revealed_evaluation;
        let stage_proof = &proof.stage_proof;
        // let seed_randomness = proof.random_field_element;
        // hasher.update(&[seed_randomness]);
        if use_poseidon {
            let mut hasher = generate_hasher();
            hasher.update(&[revealed_element]); 
            for _stage in stage_proof.iter(){
                // this is the key step, where we use the stage proof.
                // in subsequent iterations, this will be improved!
                // (notably, by using curve cycles.)
                // hasher.update(&[hash(stage[0]), hash(stage[1])]);
                stage_randomness.push(hasher.squeeze());
            }
        }
        else {
            // some code to do "stupid" randomness, which is just
            // <revealed_element, revealed_element^2,..., revealed_element^k>
            // where k=stage_proof.len().
            for _stage in stage_proof.iter(){
                match stage_randomness.last() {
                    Some(last_element) => {
                        stage_randomness.push(last_element*revealed_element);
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
// the first is the product of the last elementsof each stage_randomness vector
// the second is the square of the first.
pub fn compute_batching_randomness(proofs_of_inclusion: &[proof_of_inclusion])->[Fr; 2] {
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
    U: &G1Affine,
    vector_to_commit: &Vec<Fr>,
    z: &Fr,
    batching: bool) -> proof_of_inclusion {
    // n is the length of the vector to be commited.
    let n = g_init.len();
    assert!(check_power_of_two(n) && n == vector_to_commit.len());
    let k = int_log_2(n);
    // set up pederson commit, and the running vectors storing
    // the current a, g, b values.
    let pederson_commit = MSM(g_init, vector_to_commit);
    
    
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

    let mut L: Vec<G1Affine> = Vec::new();
    let mut R: Vec<G1Affine> = Vec::new();
    let mut stage_randomness: Vec<Fr> = Vec::new();

    // goes from step k to step 1. These are the stages
    // with numbering taken from the halo paper.
    for step in (1..k+1).rev() {

        let (L_step, R_step) = compute_L_R(
        &a_current,
        &g_current,
        &b_current, 
            U);

        L.push(L_step);
        R.push(R_step);
        // current_hash is my surrogate Fiat-Shamir.
        // this will be improved once we have curve cycles.
        // for the purposes of this experiment, I just use powers of the claimed evaluation
        // as my "hash function"
        
        // kill the use of the hasher in this iteration.
        // current_hash = hasher.squeeze();
        // replace Poseidon with the powers of current_hash as my hash function.
        current_hash *= evaluation;
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
    // I emphasize: we are using the numbering from the Halo paper!
    let stage_proof = L.iter()
                .zip(R.iter())
                .map(|(l, r)| [*l, *r])
                .collect::<Vec<[G1Affine;2]>>();
    
    let batching_helper_info = {
    if batching {
        Some(
            batching_helper_info{
                g_0,
                stage_randomness
            })
    }
    else {None}
    };
    proof_of_inclusion{
        revealed_evaluation: evaluation,
        stage_proof,
        final_a,
        batching_helper_info}
}

pub fn generate_batch_evaluation_proof(
    g_init: &Vec<G1Affine>,
    U: &G1Affine,
    vectors_to_commit: &Vec<Vec<Fr>>,
    vec_z: &Vec<Fr>,
)-> batched_proof_of_inclusion{

    assert!(vec_z.len() == vectors_to_commit.len());
    let n = g_init.len();
    let commitments = vectors_to_commit.iter()
        .map(|vector_to_commit| MSM(g_init, vector_to_commit))
        .collect::<Vec<_>>();
    
    let list_of_proofs = 
        vectors_to_commit.iter()
        .zip(vec_z.iter())
        .map(|(vector_to_commit, z)| generate_single_evaluation_proof(g_init, U, vector_to_commit, z, true))
        .collect::<Vec<_>>();
    // let proof_of_proofs = generate_single_evaluation_proof(g_init, U, vector_to_commit, z, batching)
    
    // t is the point at which we evaluate the "r-weighted polynomial"
    // For every proof \pi_i, let P_i be the "binary counting polynomial", based on the corresponding
    // stage_randomness. This is computed by the function ##compute_b_fin_poly##
    // Then the r-weighted polynomial is \sum r^i P_i.
    let [r, t] = compute_batching_randomness(&list_of_proofs);
    // batched poly = \sum r^i P_i. How do I compute P_i? It is just a vector given
    // by binary_counting_pattern_reverse of the stage_randomness_i.
    let mut weighted_polynomials: Vec<Vec<Fr>> = Vec::new();
    let mut sum_of_weighted_polynomials: Vec<Fr> = vec![Fr::zero(); n];
    let mut power_of_r = Fr::one();
    for proof in list_of_proofs.clone() {
        let stage_randomness = proof.batching_helper_info.unwrap().stage_randomness;
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
    // println!("sum of weighted polynomials: {:?}", sum_of_weighted_polynomials);
    let commitment_to_weighted_poly = MSM(g_init, &sum_of_weighted_polynomials);
    // now, we have the weighted polynomials. We need to compute the sum of these polynomials.
    // This is the batched polynomial.
    let proof_of_proofs = generate_single_evaluation_proof(g_init, U, &sum_of_weighted_polynomials, &t, false);
    batched_proof_of_inclusion {
        list_of_proofs,
        commitment_to_weighted_poly,
        proof_of_weighted_poly: proof_of_proofs,
    }
}


pub fn verify_single_evaluation_proof (
    single__IPA_proof: single__IPA_proof,
    ) -> bool {
    let commitment = &single__IPA_proof.commitment;
    let z = &single__IPA_proof.z;
    let proof = &single__IPA_proof.proof;
    let g_init = &single__IPA_proof.g_init;
    let U = &single__IPA_proof.U;
    let n = g_init.len();
    assert!(check_power_of_two(n));
    let k = int_log_2(n);
    
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
    let G_0 = MSM(g_init, &binary_counting_pattern_reverse(&stage_randomness));
    // compute b_0 
    let b_0 = compute_b_fin_poly(&z, &stage_randomness);
    // println!("b_0: {:?}", b_0);
    let mut L: Vec<G1Affine> = Vec::new();
    let mut R: Vec<G1Affine> = Vec::new();
    stage_proofs.iter().for_each(|[l, r]|{
    L.push(*l);
    R.push(*r);
    });
    // L and R are in order k..1 (same as stage_proofs).

    let w_squared = stage_randomness.iter()
                .map(|r| r.square())
                .collect::<Vec<Fr>>();
    let w_inv_squared = stage_randomness.iter()
        .map(|r| r.square().invert().unwrap())
        .collect::<Vec<Fr>>();
    let P_prime = commitment + U*revealed_evaluation;
    let first_Q = MSM(&L, &w_squared)
     + MSM(&R, &w_inv_squared)
     + P_prime;
     //println!("Rust computes first_Q as {:?}", first_Q.to_affine());
    //  println!("folded L is {:?}", MSM(&L, &w_squared));
    // println!("folded R is {:?}", MSM(&R, &w_inv_squared));
    // println!("Rust verifier computes U*b_0 as {:?}", (U*b_0).to_affine());
    // println!("Rust verifier computes G_0+U*b_0 as {:?}", (G_0 + U*b_0).to_affine());
    let second_Q = (G_0 + U*b_0)*final_a;
    println!("first_Q, is {:?}", first_Q.to_affine());
    println!("second_Q is {:?}", second_Q.to_affine());
    first_Q == second_Q
}

pub fn verify_batch_evaluation_proof(
    batched_IPA_proof: &batch_IPA_proof,
)-> bool {
    let commitments = &batched_IPA_proof.commitments;
    let vec_z = &batched_IPA_proof.vec_z;
    let batched_proof = &batched_IPA_proof.batched_proof;
    let g_init = &batched_IPA_proof.g_init;
    let U = &batched_IPA_proof.U;

    let list_of_proofs = &batched_proof.list_of_proofs;
    let commitment_to_weighted_poly = &batched_proof.commitment_to_weighted_poly;
    let proof_of_weighted_poly = &batched_proof.proof_of_weighted_poly;

    let n = g_init.len();

    let [r, t] = compute_batching_randomness(list_of_proofs);
    // steps: compute the w_i from each proof.
    // compute r and t.
    // compute the claimed evaluation of the r-weighted polynomial at t.
    // (for this, I should write a function!)
    // check the proof of this claimed evaluation

    let list_stage_randomness = list_of_proofs.iter()
        .map(|proof| compute_randomness(proof, false))
        .collect::<Vec<_>>();
    // let mut powers_of_r: Vec<Fr> = Vec::new();
    // powers_of_r.push(Fr::one());
    // for _ in 1..g_init.len() {
    //     powers_of_r.push(powers_of_r.last().unwrap()*r);
    // }
    let powers_of_r = build_poly_vector(&r, n);
    // need to check that compute_b_fin_poly is the correct code to write here.
    let claimed_evaluation = list_stage_randomness.iter()
        .zip(powers_of_r.iter())
        .map(|(stage_randomness, pow_of_r)| 
            pow_of_r * compute_b_fin_poly(&t, stage_randomness))
        .fold(Fr::zero(), |acc, x| acc + x);
    // check single proof of evaluation.

    let final_evaluation_proof = single__IPA_proof{
        commitment: *commitment_to_weighted_poly,
        z: t,
        proof: proof_of_weighted_poly.clone(),
        g_init: g_init.clone(),
        U: *U,
    };
    verify_single_evaluation_proof(final_evaluation_proof)
}


#[test]
fn test_batched_ipa(){
    let batch_size = 50;
    let k = 8;
    let n = pow(2, k);
    let mut g_init = Vec::new();
    for _ in 0..n {
        g_init.push(G1Affine::random(&mut rand::thread_rng()));
    }
    let U = G1Affine::random(&mut rand::thread_rng());
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
        .map(|vector_to_commit| MSM(&g_init, vector_to_commit))
        .collect::<Vec<G1Affine>>();
    let batched_proof = generate_batch_evaluation_proof(&g_init, &U, &vectors_to_commit, &vec_z);
    let batched_IPA_proof = batch_IPA_proof{
        commitments,
        vec_z,
        batched_proof,
        g_init: g_init.clone(),
        U: U.clone(),
    };
    let did_it_work = verify_batch_evaluation_proof(&batched_IPA_proof);
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
    let U = G1Affine::random(&mut rand::thread_rng());
    let vector_to_commit = (0..n).map(|_| 
            Fr::random(&mut rand::thread_rng())).collect::<Vec<Fr>>();
    // let vector_to_commit = (0..n).map(|l| 
    //         Fr::from(l)).collect::<Vec<Fr>>();
    // let vector_to_commit = vec![Fr::from(1000), Fr::from(2), Fr::one(), Fr::one()];
    let commitment = MSM(&g_init, &vector_to_commit);
    let z = Fr::from(1000 as u64);

    let proof = generate_single_evaluation_proof(&g_init, &U, &vector_to_commit, &z, false);
    let complete_proof = single__IPA_proof {
        commitment,
        z,
        proof,
        g_init,
        U,
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



pub fn test_ipa_export(k: usize)-> single__IPA_proof {
    let n = pow(2,k);
    let mut g_init = Vec::new();
    for _ in 0..n {
        g_init.push(G1Affine::random(&mut rand::thread_rng()));
    }
    let U = G1Affine::random(&mut rand::thread_rng());
    let vector_to_commit = (0..n).map(|_| 
            Fr::random(&mut rand::thread_rng())).collect::<Vec<Fr>>();
    // let vector_to_commit = (0..n).map(|l| 
    //         Fr::from(l)).collect::<Vec<Fr>>();
    // let vector_to_commit = vec![Fr::from(1000), Fr::from(2), Fr::one(), Fr::one()];
    let commitment = MSM(&g_init, &vector_to_commit);
    let z = Fr::from(1000);
    let proof =
        generate_single_evaluation_proof(&g_init, &U, &vector_to_commit, &z, false);
    let single_proof = 
            single__IPA_proof{
            commitment,
            z,
            proof,
            g_init,
            U,
        };
    verify_single_evaluation_proof(single_proof.clone());
    single_proof
}





#[test]
fn test_binary_counting(){
    let test_input = vec![Fr::from(1), Fr::from(2)];
    let output = binary_counting_pattern(&test_input);
   println!("The output is: {:?}", output);
   println!("For reference, the inverse of 2 is: {:?}", Fr::from(2).invert().unwrap());
}

fn main(){
    println!("Hello, world!");

}
