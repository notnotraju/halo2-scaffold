//! Example of scaffolding where function uses full `GateThreaderBuilder` instead of single `Context`

mod binary_counting;
use binary_counting::{binary_counting_reverse, binary_counting_input};

mod ipa_rust_clean;
use halo2_ecc::bigint::ProperCrtUint;
use ipa_rust_clean::{CompleteSingleIPAProof, 
    test_ipa_export, CompleteBatchIPAProof,
    test_batch_ipa_export, hash_group_to_field};

#[allow(unused_imports)]
use ark_std::{start_timer, end_timer};
use axiom_eth::rlp::builder;

use halo2_base::gates::range;
use halo2_base::halo2_proofs::plonk::Assigned;
use halo2_base::utils::bigint_to_fe;
use halo2_base::utils::biguint_to_fe;
use halo2_base::utils::fe_to_biguint;
use halo2_proofs::plonk::Circuit;


use snark_verifier::loader::halo2::IntegerInstructions;
// use poseidon_rust::Poseidon;
use snark_verifier::util::hash::OptimizedPoseidonSpec as Spec;
use snark_verifier::util::hash::Poseidon as Poseidon;
use snark_verifier::loader::native::NativeLoader;


use clap::Parser;

// halo2_ecc
use halo2_ecc::{
    fields::{FpStrategy, FieldChip},
    ecc::{
        EccChip, EcPoint},
        bn254::FpChip, bigint::CRTInteger,
};


// halo2_base

use halo2_base::{
    AssignedValue,
    Context,
    QuantumCell::{Constant, Existing, Witness},
    gates::{
        builder::{
            CircuitBuilderStage, GateThreadBuilder, MultiPhaseThreadBreakPoints,
            RangeCircuitBuilder,
        },
        RangeChip,
        GateChip,
        GateInstructions,
    },
    
    halo2_proofs::{
        arithmetic::{CurveAffine, Field, FieldExt},
        dev::MockProver,
        halo2curves::{
            bn256::{Fr, G1, G1Affine, Fq},
            group::Curve},
        plonk::{ConstraintSystem, Error},
        
    }
};

use halo2_scaffold::scaffold::{cmd::Cli, run, run_builder_on_inputs};

use ff::{PrimeField};
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};
use std::{
    fs::{self, File},
    io::{BufRead, BufReader},
};
use poseidon::PoseidonChip;



// grumpkin and group
// use grumpkin::{G1, G1Affine, Fq, Fr};

// structure for MSM circuit parameters.

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct MSMCircuitParams {
    strategy: FpStrategy,
    degree: u32,
    num_advice: usize,
    num_lookup_advice: usize,
    num_fixed: usize,
    lookup_bits: usize,
    limb_bits: usize,
    num_limbs: usize,
    batch_size: usize,
    window_bits: usize,
}

// constants for Poseidon. we don't use these in this circuit: I
// was unable to get PoseidonChip to match with a rust version of Poseidon,
// so I couldn't generate proofs to test the circuit.
// In particular, native rust implementation (in Axiom's repo) seems inconsistent
// with their PoseidonChip implementation
const T: usize = 3;
const RATE: usize = 2;
const R_F: usize = 8;
const R_P: usize = 33;


// struct containing all of the information that a verifier
// needs to check a single IPA proof. in general, our load
// method will load a proof (in whatever format) into 
// CircuitCompleteSingleProof. (note that the information here 
// is all on a circuit level.)
#[derive(Clone, Debug)]
pub struct CircuitCompleteSingleProof {
    pub commitment: EcPoint<Fr, ProperCrtUint<Fr>>,
    pub z: AssignedValue<Fr>,
    pub g_init: Vec<EcPoint<Fr, ProperCrtUint<Fr>>>,
    pub u: EcPoint<Fr, ProperCrtUint<Fr>>,
    pub revealed_evaluation: AssignedValue<Fr>,
    pub left: Vec<EcPoint<Fr, ProperCrtUint<Fr>>>,
    pub right: Vec<EcPoint<Fr, ProperCrtUint<Fr>>>,
    pub final_a: AssignedValue<Fr>,
    pub k: usize, // number, such that 2^k is the degree of the polynomial we are commiting.
                  // equivalently, the number of steps in the proof.
}

// load a CompleteSingleIPAProof, per my rust implementation, 
// into a CircuitCompleteSingleProof.

pub fn load_complete_single_ipa_proof(
    builder: &mut GateThreadBuilder<Fr>,
    gate: &GateChip<Fr>,
    range: &RangeChip<Fr>,
    params: &MSMCircuitParams,
    single_proof: &CompleteSingleIPAProof, // an IPA proof, generated in rust.
    make_public: &mut Vec<AssignedValue<Fr>>,
) -> CircuitCompleteSingleProof {
    let fp_chip = FpChip::<Fr>::new(range, params.limb_bits, params.num_limbs);
    let ecc_chip = EccChip::new(&fp_chip);

    // obtain context.
    let ctx = builder.main(0);
    
    // load the various inputs.
    let commitment = ecc_chip.load_private::<G1Affine>(
            ctx, (single_proof.commitment.x, single_proof.commitment.y));
    
    let z = ctx.load_witness(single_proof.z);
    let g_init = 
        single_proof.
        g_init.
        iter().
        map(|base| ecc_chip.load_private::<G1Affine>(ctx, (base.x, base.y)))
        .collect::<Vec<_>>();
    
    let u = ecc_chip.load_private::<G1Affine>(ctx, (single_proof.u.x, single_proof.u.y));
    

    let revealed_evaluation = ctx.load_witness(single_proof.proof.revealed_evaluation);

    make_public.push(revealed_evaluation);
    make_public.push(z);

    let stage_proof = single_proof.proof.stage_proof.
        iter().
        map(|proof| [ecc_chip.load_private::<G1Affine>(ctx, (proof[0].x, proof[0].y)), 
                                    ecc_chip.load_private::<G1Affine>(ctx, (proof[1].x, proof[1].y))])
        .collect::<Vec<_>>();
    // process left and right.

    let left = stage_proof.iter()
                    .map(|proof| proof[0].clone())
                    .collect::<Vec<_>>();
    let right = stage_proof.iter()
                    .map(|proof| proof[1].clone())
                    .collect::<Vec<_>>();


    let final_a = ctx.load_witness(single_proof.proof.final_a);
    let k = left.len();
    CircuitCompleteSingleProof {
        commitment,
        z,
        g_init,
        u,
        revealed_evaluation,
        left,
        right,
        final_a,
        k
    }
}

// "hash" a point p on the curve to an F_r point.
// we simply take the p.x and p.y points "mod r"
// (which is what is meant by p.x.native, under the CRTInteger<Fr>
// abstraction), and add them. 
pub fn hash_group_to_field_circuit(
    // builder: &mut GateThreadBuilder<Fr>,
    ctx: &mut Context<Fr>,
    gate: &GateChip<Fr>,
    p: EcPoint<Fr, ProperCrtUint<Fr>>
  )->AssignedValue<Fr>{
    let x = p.x.native();
    let y = p.y.native();
    gate.add(ctx, *x, *y)    
  }

  pub fn test_msm(
    builder: &mut GateThreadBuilder<Fr>,
    (p, s): (Vec<G1Affine>, Vec<Fr>),
    make_public: &mut Vec<AssignedValue<Fr>>,
  ){
    let path = "examples/msm_circuit.config";
    let params: MSMCircuitParams = serde_json::from_reader(
        File::open(path).unwrap_or_else(|e| panic!("{path} does not exist: {e:?}")),
    )
    .unwrap();
    let gate = GateChip::<Fr>::default();
    let range = RangeChip::<Fr>::default(params.lookup_bits);
    let fp_chip = FpChip::<Fr>::new(&range, params.limb_bits, params.num_limbs);
    let ecc_chip = EccChip::new(&fp_chip);
            // obtain context.
    let ctx = builder.main(0);
    let p = 
        p
        .iter()
        .map(|base| ecc_chip.load_private::<G1Affine>(ctx, (base.x, base.y)))
        .collect::<Vec<_>>();
    let s = s.iter().map(|x| vec![ctx.load_witness(*x)]).collect::<Vec<_>>();
    let out = ecc_chip.variable_base_msm_in::<G1Affine>(builder, &p, s, Fr::NUM_BITS as usize, 4, 0);
   
  }


// given some part of the proof, complete the "stage_randomness"
// (this is where the verifier simulates the Fiat-Shamir.)
// in particular, the output will be of the form:
// (<w_k, ..., w_1>, <w_k^{-1}, ..., w_1^{-1}>), with constraints
// forcing w_i * w_i^{-1} = 1.
// as always, the numbering corresponds to the stages.
pub fn compute_stage_randomness_single_proof(
    builder: &mut GateThreadBuilder<Fr>,
    gate: &GateChip<Fr>,
    z: AssignedValue<Fr>,
    revealed_evaluation: AssignedValue<Fr>,
    left: Vec<EcPoint<Fr, ProperCrtUint<Fr>>>,
    right: Vec<EcPoint<Fr, ProperCrtUint<Fr>>>,
    k: usize,
)->(Vec<AssignedValue<Fr>>, Vec<AssignedValue<Fr>>){

    let mut stage_randomness = Vec::new();
    let mut stage_randomness_inv = Vec::new();
    let ctx = builder.main(0);

    // ideally, this will use Poseidon at some point. below I have
    // a bit of code setting up the PoseidonChip.
    // let mut poseidon = PoseidonChip::<Fr, T, RATE>::new(ctx, R_F, R_P).unwrap();
    // poseidon.update(&[revealed_evaluation]);
    
    // INSTEAD, our randomness is given inductively by the formula below.
    // stage_randomness[0]=revealed evaluation.
    // stage_randomness[i] = 
    //      stage_randomness[i-1] * revealed_evaluation + hash(left[i]) + hash(right[i])
    stage_randomness.push(revealed_evaluation);
    let r = revealed_evaluation.value();
    for i in 1..k{
        
        let scale_old_randomness = gate.mul(ctx, 
            revealed_evaluation, stage_randomness[i-1]);
        let left_hash = hash_group_to_field_circuit(ctx, gate, left[i].clone());
        let right_hash = hash_group_to_field_circuit(ctx, gate, right[i].clone());
        let preliminary_randomness = gate.add(ctx, scale_old_randomness, left_hash);
        let new_randomness = gate.add(ctx, preliminary_randomness, right_hash);
        stage_randomness.push(new_randomness);
    }
    for i in 0..k{
        let pow_r_inv = stage_randomness[i].value().invert().unwrap();
        stage_randomness_inv.push(ctx.load_witness(pow_r_inv));
        let _val_assigned =
        ctx.assign_region_last([Constant(Fr::zero()), 
                                Existing(stage_randomness[i]),
                                Existing(stage_randomness_inv[i]),
                                Constant(Fr::one())], [0]);
    }
    (stage_randomness, stage_randomness_inv)
}

// compute the "batching" randomness, i.e., given a bunch of proofs,
// compute [r,t], where we will weight the polynomials by r and evaluate at t.
// m is len(vec_stage_randomness), i.e., the number of proofs being batched.
pub fn compute_final_batching_randomness(
    builder: &mut GateThreadBuilder<Fr>,
    gate: &GateChip<Fr>,
    vec_stage_randomness: Vec<Vec<AssignedValue<Fr>>>,
    m: usize,
    k: usize,
)->[AssignedValue<Fr>; 2]{
    let ctx = builder.main(0);
    let mut compute_r: Vec<AssignedValue<Fr>> = Vec::new();
    compute_r.push(vec_stage_randomness[0][k-1]);
    for i in 1..m{
        let new_randomness = gate.mul(ctx, 
            compute_r[i-1], vec_stage_randomness[i][k-1]);
        compute_r.push(new_randomness);
    }
    let t = gate.mul(ctx, compute_r[m-1], compute_r[m-1]);
    [compute_r[m-1], t]
}

// given stage_randomness = (w_k, w_{k-1},...,w_1) and z\in F_r, compute the following:
// \Prod_{i=1}^k (z^{2^{i-1}} * w_i + w_i^{-1})
pub fn evaluate_folded_product_poly(
    ctx: &mut Context<Fr>,
    gate: &GateChip<Fr>,
    z: AssignedValue<Fr>,
    stage_randomness: Vec<AssignedValue<Fr>>,
    stage_randomness_inv: Vec<AssignedValue<Fr>>,
)->AssignedValue<Fr>{
    // two_pow_of_z = [z^{2^{k-1}}, z^{2^{k-2}}, ..., z^{2^0}}]
    let k = stage_randomness.len();
    let mut two_pow_of_z: Vec<AssignedValue<Fr>> = Vec::new();
    two_pow_of_z.push(z);
    for i in 1..k {
        two_pow_of_z.push(
            gate.mul(ctx,
                two_pow_of_z[i-1], 
                two_pow_of_z[i-1]));
    }
    two_pow_of_z.reverse();

    // compute the desired output using the truncated product expansion
    // set partial_evaluation[0] = 2^{k-1} * w_k + w_k^{-1}
    // then build gates to iteratively compute the rest of the product
    let mut partial_evaluation: Vec<AssignedValue<Fr>> = Vec::new();
    partial_evaluation.push(gate.mul_add(
        ctx,  stage_randomness[0], two_pow_of_z[0], stage_randomness_inv[0],));
   
    for i in 1..k {
        let _aux_new_val = gate.mul_add(
            ctx, stage_randomness[i], two_pow_of_z[i],  stage_randomness_inv[i]);
        partial_evaluation.push(
            gate.mul(ctx, _aux_new_val, partial_evaluation[i-1])
        );
    }
    partial_evaluation[k-1]
}



// verify a single IPA proof. Input is of type CompleteSingleIPAProof.
// I make z and the revealed_evaluation public.
// (I don't know how to make the commitment public!!)
fn verify_single_ipa_proof(
    builder: &mut GateThreadBuilder<Fr>,
    // params: &MSMCircuitParams,
    single_proof: CompleteSingleIPAProof,
    make_public: &mut Vec<AssignedValue<Fr>>,
){
    let path = "examples/msm_circuit.config";
    let params: MSMCircuitParams = serde_json::from_reader(
        File::open(path).unwrap_or_else(|e| panic!("{path} does not exist: {e:?}")),
    )
    .unwrap();

    // set up chips.
    std::env::set_var("LOOKUP_BITS", params.lookup_bits.to_string());
    let gate = GateChip::<Fr>::default();
    let range = RangeChip::<Fr>::default(params.lookup_bits);
    let fp_chip = FpChip::<Fr>::new(&range, params.limb_bits, params.num_limbs);
    let ecc_chip = EccChip::new(&fp_chip);

    // obtain context.
    let ctx = builder.main(0);

    // load the various inputs from single_proof.
    let complete_assigned_proof = 
        load_complete_single_ipa_proof(builder, &gate, &range, &params, &single_proof, make_public);
    
    // introduce variables for the inputs.
    let ctx = builder.main(0);
    let commitment = complete_assigned_proof.commitment;
    let z = complete_assigned_proof.z;
    let g_init = complete_assigned_proof.g_init;
    let u = complete_assigned_proof.u;
    let revealed_evaluation = complete_assigned_proof.revealed_evaluation;
    
    // load left, right, and final_a.
    let left = complete_assigned_proof.left;
    let right = complete_assigned_proof.right;
    let final_a = complete_assigned_proof.final_a;
    let ctx = builder.main(0);
    // set up k and compute stage_randomness.
    let k = complete_assigned_proof.k;
    // compute stage_randomness
    let (stage_randomness, stage_randomness_inv) = 
        compute_stage_randomness_single_proof(
            builder,
            &gate,
            z,
            revealed_evaluation,
            left.clone(),
            right.clone(),
            k);
    let ctx = builder.main(0);
    
    println!("we have loaded all of the inputs!");
    
    let mut stage_randomness_sq: Vec<AssignedValue<Fr>> = Vec::new();
    let mut stage_randomness_inv_sq: Vec<AssignedValue<Fr>> = Vec::new();
    for i in 0..k {
        stage_randomness_sq.push(gate.mul(ctx, stage_randomness[i], stage_randomness[i]));
        stage_randomness_inv_sq.push(gate.mul(ctx, stage_randomness_inv[i], stage_randomness_inv[i]));
    }
    // compute b_0
    let b_0 = evaluate_folded_product_poly(
        ctx,
        &gate,
        z,
        stage_randomness.clone(),
        stage_randomness_inv
    );

    // compute the binary counting pattern of the stage_randomness.s
    let s = binary_counting_reverse(
        ctx, &gate, 
        binary_counting_input::<Fr>{
            field_elts: stage_randomness,}); 

    // not sure what ``window bits'' is, only used for MSM.
    let window_bits = 4;

    // intermediary in computation of p_prime.
    let u_x_revealed = 
        ecc_chip.scalar_mult(ctx,
                            u.clone(), 
                            vec![revealed_evaluation],
                            Fr::NUM_BITS as usize,
                            window_bits,
                            true);
    
    let p_prime =
            ecc_chip.add_unequal(ctx, &commitment, &u_x_revealed, true);
    // println!("Circuit managed to compute p_prime! The value is {:?}, {:?}", bigint_to_fe::<Fr>(&p_prime.x.value), bigint_to_fe::<Fr>(&p_prime.y.value));
    
    // do MSM's with left, right and add to p_prime.
    let left_folded = ecc_chip.
        variable_base_msm_in::<G1Affine>(
            builder, 
            &left,
            stage_randomness_sq.iter().map(|x| vec![*x]).collect::<Vec<_>>(),
            Fr::NUM_BITS as usize,
            window_bits,
            0);
    
    let right_folded = ecc_chip.
        variable_base_msm_in::<G1Affine>(
            builder, 
            &right,
            stage_randomness_inv_sq.iter().map(|x| vec![*x]).collect::<Vec<_>>(),
            Fr::NUM_BITS as usize,
            window_bits,
            0);

    // let ctx = builder.main(0);
    let g_0 = ecc_chip.
        variable_base_msm_in::<G1Affine>(
            builder, 
            &g_init,
            s.iter().map(|x| vec![*x]).collect::<Vec<_>>(),
            Fr::NUM_BITS as usize,
            window_bits,
         0);

    let ctx = builder.main(0);

    let left_folded_plus_right_folded = ecc_chip.add_unequal(ctx, &left_folded, &right_folded, true);
    let first_q = ecc_chip.add_unequal(ctx, &left_folded_plus_right_folded, &p_prime, true);
    // ub_0
    let u_x_b_0 = ecc_chip.scalar_mult(ctx,
                            u, 
                            vec![b_0],
                            Fr::NUM_BITS as usize,
                            window_bits,
                            true);
    // println!("Circuit computes u_x_b_0: {:?}, {:?}", bigint_to_fe::<Fr>(&u_x_b_0.x.value), bigint_to_fe::<Fr>(&u_x_b_0.y.value)  );
    let g0_plus_ub0 = ecc_chip.add_unequal(ctx,
        &g_0,
        &u_x_b_0,
        true);
    //println!("Circuit computes g0_plus_ub0: {:?}, {:?}", bigint_to_fe::<Fr>(&g0_plus_ub0.x.value), bigint_to_fe::<Fr>(&g0_plus_ub0.y.value)  );
    let second_q = ecc_chip.scalar_mult(ctx,
                            g0_plus_ub0, 
                            vec![final_a],
                            Fr::NUM_BITS as usize,
                            window_bits,
                            true);
    // println!("Circuit computes first_q: {:?}, {:?}", bigint_to_fe::<Fr>(&first_q.x.value), bigint_to_fe::<Fr>(&first_q.y.value)  );
    // println!("Circuit computes second_q: {:?}, {:?}", bigint_to_fe::<Fr>(&second_q.x.value), bigint_to_fe::<Fr>(&second_q.y.value)  );
    // for sanity, print out the differences between the coordinates.
    println!("Difference between the coordinates: {:?}, {:?}",
        first_q.x.native().value() - second_q.x.native().value(), 
        first_q.y.native().value() - second_q.y.native().value());
    // assert that the two points are equal. (Q: should I use an IsEqual gate instead?)
    let out = ecc_chip.is_equal(ctx, first_q.clone(), second_q.clone());
    make_public.push(out);
    // not sure if I need/want this!
    ecc_chip.assert_equal(ctx, first_q, second_q);
}

// structure containing everything a verifier needs to verifier
// a batch proof.
pub struct CircuitCompleteBatchProof {
    // the proofs of the individual claims
    pub vec_commitment: Vec<EcPoint<Fr, ProperCrtUint<Fr>>>,
    pub vec_z: Vec<AssignedValue<Fr>>,
    pub g_init: Vec<EcPoint<Fr, ProperCrtUint<Fr>>>,
    pub u: EcPoint<Fr, ProperCrtUint<Fr>>,
    pub vec_revealed_evaluation: Vec<AssignedValue<Fr>>,
    pub vec_left: Vec<Vec<EcPoint<Fr, ProperCrtUint<Fr>>>>,
    pub vec_right: Vec<Vec<EcPoint<Fr, ProperCrtUint<Fr>>>>,
    pub vec_a_0: Vec<AssignedValue<Fr>>,
    pub vec_g_0: Vec<EcPoint<Fr, ProperCrtUint<Fr>>>, // this is new for batching!
    // the final "blended" proof.
    pub final_commitment: EcPoint<Fr, ProperCrtUint<Fr>>,
    pub final_left: Vec<EcPoint<Fr, ProperCrtUint<Fr>>>,
    pub final_right: Vec<EcPoint<Fr, ProperCrtUint<Fr>>>,
    pub final_a_0: AssignedValue<Fr>,
    pub k: usize,
    pub m: usize,    
}

pub fn load_complete_batch_ipa_proof(
    builder: &mut GateThreadBuilder<Fr>,
    gate: &GateChip<Fr>,
    range: &RangeChip<Fr>,
    params: &MSMCircuitParams,
    proof: &CompleteBatchIPAProof,
    make_public: &mut Vec<AssignedValue<Fr>>
)->CircuitCompleteBatchProof{

    let fp_chip = FpChip::<Fr>::new(range, params.limb_bits, params.num_limbs);
    let ecc_chip = EccChip::new(&fp_chip);
    let ctx = builder.main(0);
    let vec_commitment = proof.commitments
                        .iter()
                        .map(|p| ecc_chip.load_private::<G1Affine>( ctx, (p.x,p.y)))
                        .collect::<Vec<_>>();
    let vec_z = proof.vec_z
                        .iter()
                        .map(|x| ctx.load_witness(*x))
                        .collect::<Vec<_>>();
    let g_init = proof.g_init
                        .iter()
                        .map(|p| ecc_chip.load_private::<G1Affine>( ctx, (p.x,p.y)))
                        .collect::<Vec<_>>();
    let u = ecc_chip.load_private::<G1Affine>( ctx, (proof.u.x, proof.u.y));
    let vec_revealed_evaluation = proof.batch_proof
                        .list_of_proofs
                        .iter()
                        .map(|x| ctx.load_witness(x.revealed_evaluation))
                        .collect::<Vec<_>>();
    let vec_left = proof.batch_proof
                        .list_of_proofs
                        .iter()
                        .map(|x| x.stage_proof
                            .iter()
                            .map(|p| ecc_chip.load_private::<G1Affine>(ctx,
                                 (p[0].x,p[0].y)))
                            .collect::<Vec<_>>())
                        .collect::<Vec<_>>();
    let vec_right = proof.batch_proof
                    .list_of_proofs
                    .iter()
                    .map(|x| x.stage_proof
                        .iter()
                        .map(|p| ecc_chip.load_private::<G1Affine>(ctx,
                             (p[1].x,p[1].y)))
                        .collect::<Vec<_>>())
                    .collect::<Vec<_>>();
    let vec_a_0 = proof.batch_proof
                    .list_of_proofs
                    .iter()
                    .map(|x| ctx.load_witness(x.final_a))
                    .collect::<Vec<_>>();
    let vec_g_0 = proof.batch_proof
                    .list_of_proofs
                    .iter()
                    .map(|proof| {
                        match proof.batching_helper_info{
                            Some(ref p) => ecc_chip.load_private::<G1Affine>(ctx, (p.g_0.x, p.g_0.y)),
                            None => panic!("Batching helper info is missing!")
                        }})
                    .collect::<Vec<_>>();
    
    // load the final proof.
    let final_commitment =
        ecc_chip.load_private::<G1Affine>(ctx, (proof.batch_proof.commitment_to_weighted_poly.x, proof.batch_proof.commitment_to_weighted_poly.y));
    let final_left = proof.batch_proof.proof_of_weighted_poly
                        .stage_proof.iter()
                        .map(|p| ecc_chip.load_private::<G1Affine>(ctx,
                             (p[0].x,p[0].y)))
                        .collect::<Vec<_>>();
    let final_right = proof.batch_proof.proof_of_weighted_poly
                        .stage_proof.iter()
                        .map(|p| ecc_chip.load_private::<G1Affine>(ctx,
                             (p[1].x,p[1].y)))
                        .collect::<Vec<_>>();
    let final_a_0 = ctx.load_witness(proof.batch_proof.proof_of_weighted_poly.final_a);
    let k = final_left.len(); // modify? 
    let m = vec_left.len(); // modify
    CircuitCompleteBatchProof{
        vec_commitment,
        vec_z,
        g_init,
        u,
        vec_revealed_evaluation,
        vec_left,
        vec_right,
        vec_a_0,
        vec_g_0,
        final_commitment,
        final_left,
        final_right,
        final_a_0,
        k,
        m
    }
}

// batch verification. input is a CircuitCompleteBatchProof.
pub fn verify_batch_ipa_proof(
    builder: &mut GateThreadBuilder<Fr>,
    // params: &MSMCircuitParams,
    complete_batch_ipa_proof: CompleteBatchIPAProof,
    make_public: &mut Vec<AssignedValue<Fr>>,
){
    let path = "examples/msm_circuit.config";
    let params: MSMCircuitParams = serde_json::from_reader(
        File::open(path).unwrap_or_else(|e| panic!("{path} does not exist: {e:?}")),
    )
    .unwrap();

    // set up chips.
    std::env::set_var("LOOKUP_BITS", params.lookup_bits.to_string());
    let gate = GateChip::<Fr>::default();
    let range = RangeChip::<Fr>::default(params.lookup_bits);
    // let fp_chip = FpChip::<Fr>::new(&range, params.limb_bits, params.num_limbs);
    // let ecc_chip = EccChip::new(&fp_chip);

    // obtain context.
    let ctx = builder.main(0);
    let circuit_batch_ipa_proof = load_complete_batch_ipa_proof(
        builder,
        &gate,
        &range,
        &params,
        &complete_batch_ipa_proof,
        make_public,
    );
    // get access to the inputs.
    let _vec_commitment = circuit_batch_ipa_proof.vec_commitment;
    let vec_z = circuit_batch_ipa_proof.vec_z;
    let _g_init = circuit_batch_ipa_proof.g_init;
    let _u = circuit_batch_ipa_proof.u;
    let vec_revealed_evaluation = circuit_batch_ipa_proof.vec_revealed_evaluation;
    let vec_left = circuit_batch_ipa_proof.vec_left;
    let vec_right = circuit_batch_ipa_proof.vec_right;
    let _vec_a_0 = circuit_batch_ipa_proof.vec_a_0;
    let _vec_g_0 = circuit_batch_ipa_proof.vec_g_0;
    let _final_commitment = circuit_batch_ipa_proof.final_commitment;
    let _final_left = circuit_batch_ipa_proof.final_left;
    let _final_right = circuit_batch_ipa_proof.final_right;
    let _final_a_0 = circuit_batch_ipa_proof.final_a_0;
    let k = circuit_batch_ipa_proof.k;
    let m = circuit_batch_ipa_proof.m;

    // compute the stage_randomness at each stage.
    let mut vec_stage_randomness: Vec<Vec<AssignedValue<Fr>>> = Vec::new();
    let mut vec_stage_randomness_inv: Vec<Vec<AssignedValue<Fr>>> = Vec::new();


    for i in 0..m {
        let (stage_randomness, stage_randomness_inv) = 
            compute_stage_randomness_single_proof(builder, &gate, vec_z[i], vec_revealed_evaluation[i], vec_left[i].clone(), vec_right[i].clone(), k);
        vec_stage_randomness.push(stage_randomness);
        vec_stage_randomness_inv.push(stage_randomness_inv);
    }
    // compute the final randomness myself!
    let [r, t] = 
        compute_final_batching_randomness(builder, &gate, vec_stage_randomness.clone(), m, k);
    let ctx = builder.main(0);

    // compute the claimed final evaluation.
    let mut pow_of_r: Vec<AssignedValue<Fr>> = Vec::new();
    pow_of_r.push(ctx.load_constant(Fr::one()));
    for i in 1..m {
        pow_of_r.push(gate.mul(ctx, pow_of_r[i-1], r));
    }
    // a vector which records the computation of the final evaluation.
    let mut partial_evaluations: Vec<AssignedValue<Fr>> = Vec::new();
    partial_evaluations.push(ctx.load_constant(Fr::zero()));
    for i in 0..m {
        let bare_stage_i_evaluation =
            evaluate_folded_product_poly(
                ctx, 
                &gate,
                t, 
                vec_stage_randomness[i].clone(), 
                vec_stage_randomness_inv[i].clone());
        partial_evaluations.push(
            gate.mul_add(ctx, pow_of_r[i], bare_stage_i_evaluation, partial_evaluations[i])
        );
    }

    let final_claimed_evaluation = partial_evaluations[m];
    println!("final_claimed_evaluation: {:?}", final_claimed_evaluation.value());
    let final_proof = CompleteSingleIPAProof{
        commitment: complete_batch_ipa_proof.batch_proof.commitment_to_weighted_poly,
        z: *t.value(),
        proof: complete_batch_ipa_proof.batch_proof.proof_of_weighted_poly,
        g_init: complete_batch_ipa_proof.g_init,
        u: complete_batch_ipa_proof.u,
    };
    // now just have to verify the single proof, with respect to this claimed evaluation.
    // NOTE: there is an ``out'' variable that has been made_public. we
    // should check that is 1.
    verify_single_ipa_proof(builder, final_proof, make_public);
    
  }


fn main() {
    std::env::set_var("RUST_BACKTRACE", "1");
    env_logger::init();

    let args = Cli::parse();
    let path = "examples/msm_circuit.config";
    let params: MSMCircuitParams = serde_json::from_reader(
        File::open(path).unwrap_or_else(|e| panic!("{path} does not exist: {e:?}")),
    )
    .unwrap();
    std::env::set_var("LOOKUP_BITS", params.lookup_bits.to_string());
    std::env::set_var("DEGREE", 4.to_string());
    let private_inputs = test_ipa_export(4);
    let random_group_element = G1Affine::random(&mut OsRng);
    let random_group_elements = (0..256).map(|_| G1Affine::random(&mut OsRng)).collect::<Vec<_>>();
    let random_scalars = (0..256).map(|_| Fr::random(&mut OsRng)).collect::<Vec<_>>();
    let batch_private_inputs = test_batch_ipa_export(2,10);
    // run_builder_on_inputs(verify_single_ipa_proof_hack, args, private_inputs);
    // let random_point = G1Affine::random(&mut OsRng);
    //run_builder_on_inputs(verify_single_ipa_proof, args, private_inputs);
    // run_builder_on_inputs(verify_batch_ipa_proof, args, batch_private_inputs);
    // run_builder_on_inputs(group_to_field, args, random_group_element);
    run_builder_on_inputs(test_msm, args, (random_group_elements, random_scalars));
}



