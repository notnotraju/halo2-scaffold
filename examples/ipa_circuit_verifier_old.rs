//! Example of scaffolding where function uses full `GateThreaderBuilder` instead of single `Context`

mod binary_counting;
mod ipa_rust_simple_hash_batch;
// use crate::binary_counting::binary_counting;


#[allow(unused_imports)]
use ark_std::{start_timer, end_timer};
use axiom_eth::rlp::builder;
use binary_counting::{binary_counting_reverse, binary_counting_input};
use halo2_base::utils::bigint_to_fe;
use ipa_rust_simple_hash_batch::{proof_of_inclusion, single__IPA_proof, 
                                test_ipa_export, generate_hasher,
                                batch_IPA_proof};

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
// in this code, these global constants are not necessary.
// they are used to uniformize the potential application of Poseidon
// for Fiat-Shamir.
const T: usize = 3;
const RATE: usize = 2;
const R_F: usize = 8;
const R_P: usize = 33;


// currently, the input is of type single__IPA_proof
// this is bad, because the length is not specified by some global constant.
// the vectorized inputs are: g_init, stage_proofs, and then
// in batching_helper info, the value of stage_randomness.
fn verify_single_IPA_proof(
    builder: &mut GateThreadBuilder<Fr>,
    // params: &MSMCircuitParams,
    single_proof: single__IPA_proof,
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

    // load the various inputs.
    let commitment = ecc_chip.load_private(
                ctx, (single_proof.commitment.x, single_proof.commitment.y));
    let z = ctx.load_witness(single_proof.z);
    let g_init = 
        single_proof.
        g_init.
        iter().
        map(|base| ecc_chip.load_private(ctx, (base.x, base.y)))
        .collect::<Vec<_>>();
    let U = ecc_chip.load_private(ctx, (single_proof.U.x, single_proof.U.y));
    let revealed_evaluation = ctx.load_witness(single_proof.proof.revealed_evaluation);
    
    let stage_proof = single_proof.proof.stage_proof.
        iter().
        map(|proof| [ecc_chip.load_private(ctx, (proof[0].x, proof[0].y)), ecc_chip.load_private(ctx, (proof[1].x, proof[1].y))])
        .collect::<Vec<_>>();
    // process L, and R.

    let L = stage_proof.iter()
                        .map(|proof| proof[0].clone())
                        .collect::<Vec<_>>();
    let R = stage_proof.iter()
                        .map(|proof| proof[1].clone())
                        .collect::<Vec<_>>();
    let final_a = ctx.load_witness(single_proof.proof.final_a);
    println!("we have loaded all of the inputs!");
    // build the poseidon chip.
    // let mut poseidon = PoseidonChip::<Fr, T, RATE>::new(ctx, R_F, R_P).unwrap();
    // regenerate the randomness from the proof. KILLED POSEIDON
    // for testing purposes
    // note that I'm doing a particularly dumb version of this atm.
    // poseidon.update(&[revealed_evaluation]);
    
    // in this version, the ith entry of stage_randomness is 
    // the randomness at the k_minus_i stage. (so, the 0th entry is
    // the randomness obtained *as a result* of stage k.)
    let mut stage_randomness: Vec<AssignedValue<Fr>> = Vec::new();
    let mut stage_randomness_inv: Vec<AssignedValue<Fr>> = Vec::new();
    let k = stage_proof.len();
    for i in 0..k {
        // in the *correct* version of this, somewhere in this loop
        // I will need to update the poseidon chip.
        // stage_randomness.push(poseidon.squeeze(ctx, &gate).unwrap());
        // in the below code, I have my randomness is just powers of the revealed_evaluation.
        if i==0 {
            stage_randomness.push(revealed_evaluation);
        }
        else {
            stage_randomness.push(
                gate.mul(ctx, revealed_evaluation, stage_randomness[i-1]))
        }
        let r_inv = stage_randomness[i].value().invert().unwrap();
        stage_randomness_inv.push(ctx.load_witness(r_inv));
        // ensure the relation that stage_random[i] and stage_random_inv[i] are inverses.
        let _val_assigned =
        ctx.assign_region_last([Constant(Fr::zero()), 
                                Existing(stage_randomness[i]),
                                Existing(stage_randomness_inv[i]),
                                Constant(Fr::one())],
                                [0]);
    }
    let mut stage_randomness_sq: Vec<AssignedValue<Fr>> = Vec::new();
    let mut stage_randomness_inv_sq: Vec<AssignedValue<Fr>> = Vec::new();
    for i in 0..k {
        stage_randomness_sq.push(gate.mul(ctx, stage_randomness[i], stage_randomness[i]));
        stage_randomness_inv_sq.push(gate.mul(ctx, stage_randomness_inv[i], stage_randomness_inv[i]));
    }
    // compute b_0. This involves O(k) steps, via the compact
    // representation of polynomial.
    let mut two_pow_of_z: Vec<AssignedValue<Fr>> = Vec::new();
    two_pow_of_z.push(z);
    for i in 1..k {
        two_pow_of_z.push(
            gate.mul(ctx,
                two_pow_of_z[i-1], 
                two_pow_of_z[i-1]));
    }
    two_pow_of_z.reverse();
    let mut evaluate_b_0: Vec<AssignedValue<Fr>> = Vec::new();
    evaluate_b_0.push(gate.mul_add(
        ctx,  stage_randomness[0], two_pow_of_z[0], stage_randomness_inv[0],));
   
    for i in 1..k {
        let _aux_new_val = gate.mul_add(
            ctx, stage_randomness[i], two_pow_of_z[i],  stage_randomness_inv[i]);
        evaluate_b_0.push(
            gate.mul(ctx, _aux_new_val, evaluate_b_0[i-1])
        );
    }

    let b_0 = evaluate_b_0[k-1];
    let s = binary_counting_reverse(
        ctx, &gate, 
        binary_counting_input::<Fr>{
            field_elts: stage_randomness,}); 

    // not sure what ``window bits'' is, only used for MSM.
    let window_bits = 4;

    // intermediary in computation of P_Prime.
    let U_x_revealed = 
        ecc_chip.scalar_mult(ctx,
                            &U, 
                            vec![revealed_evaluation],
                            Fr::NUM_BITS as usize,
                            window_bits);
    
    let P_Prime =
            ecc_chip.add_unequal(ctx, &commitment, &U_x_revealed, true);
    // println!("Circuit managed to compute P_Prime! The value is {:?}, {:?}", bigint_to_fe::<Fr>(&P_Prime.x.value), bigint_to_fe::<Fr>(&P_Prime.y.value));
    
    // do MSM's with L, R and add to P_Prime.
    let L_folded = ecc_chip.
        variable_base_msm_in::<G1Affine>(
            builder, 
            &L,
            stage_randomness_sq.iter().map(|x| vec![*x]).collect::<Vec<_>>(),
            Fr::NUM_BITS as usize,
            window_bits,
            0);
    
    let R_folded = ecc_chip.
        variable_base_msm_in::<G1Affine>(
            builder, 
            &R,
            stage_randomness_inv_sq.iter().map(|x| vec![*x]).collect::<Vec<_>>(),
            Fr::NUM_BITS as usize,
            window_bits,
            0);

    // println!("Circuit managed to compute L_folded! The value is {:?}, {:?}", bigint_to_fe::<Fr>(&L_folded.x.value), bigint_to_fe::<Fr>(&L_folded.y.value)  );
    // println!("Circuit managed to compute R_folded! The value is {:?}, {:?}", bigint_to_fe::<Fr>(&R_folded.x.value), bigint_to_fe::<Fr>(&R_folded.y.value)  );
    let ctx = builder.main(0);
    let G_0 = ecc_chip.
        variable_base_msm_in::<G1Affine>(
            builder, 
            &g_init,
            s.iter().map(|x| vec![*x]).collect::<Vec<_>>(),
            Fr::NUM_BITS as usize,
            window_bits,
         0);

    let ctx = builder.main(0);

    let L_folded_plus_R_folded = ecc_chip.add_unequal(ctx, &L_folded, &R_folded, true);
    let first_Q = ecc_chip.add_unequal(ctx, &L_folded_plus_R_folded, &P_Prime, true);
    
    let U_x_b_0 = ecc_chip.scalar_mult(ctx,
                            &U, 
                            vec![b_0],
                            Fr::NUM_BITS as usize,
                            window_bits);
    // println!("Circuit computes U_x_b_0: {:?}, {:?}", bigint_to_fe::<Fr>(&U_x_b_0.x.value), bigint_to_fe::<Fr>(&U_x_b_0.y.value)  );
    let g0_plus_ub0 = ecc_chip.add_unequal(ctx,
        &G_0,
        &U_x_b_0,
        true);
    //println!("Circuit computes g0_plus_ub0: {:?}, {:?}", bigint_to_fe::<Fr>(&g0_plus_ub0.x.value), bigint_to_fe::<Fr>(&g0_plus_ub0.y.value)  );
    let second_Q = ecc_chip.scalar_mult(ctx,
                            &g0_plus_ub0, 
                            vec![final_a],
                            Fr::NUM_BITS as usize,
                            window_bits);
    // println!("Circuit computes first_Q: {:?}, {:?}", bigint_to_fe::<Fr>(&first_Q.x.value), bigint_to_fe::<Fr>(&first_Q.y.value)  );
    // println!("Circuit computes second_Q: {:?}, {:?}", bigint_to_fe::<Fr>(&second_Q.x.value), bigint_to_fe::<Fr>(&second_Q.y.value)  );
    // println!("Difference between the coordinates: {:?}, {:?}",
    //     &first_Q.x.value - &second_Q.x.value, 
    //     &first_Q.y.value - &second_Q.y.value);
    ecc_chip.assert_equal(ctx, &first_Q, &second_Q);
}

#[derive(Clone, Debug)]
pub struct assigned_proof_of_inclusion{
    pub revealed_evaluation: AssignedValue<Fr>,
    L: Vec<EcPoint<Fr, CRTInteger<Fr>>>,
    R: Vec<EcPoint<Fr, CRTInteger<Fr>>>,
    final_a: AssignedValue<Fr>,
}


pub fn load_proof_of_inclusion(
    builder: &mut GateThreadBuilder<Fr>,
    proof: &proof_of_inclusion,
    make_public: &mut Vec<AssignedValue<Fr>>
) -> assigned_proof_of_inclusion{
    let path = "examples/msm_circuit.config";
    let params: MSMCircuitParams = serde_json::from_reader(
        File::open(path).unwrap_or_else(|e| panic!("{path} does not exist: {e:?}")),
    )
    .unwrap();

    std::env::set_var("LOOKUP_BITS", params.lookup_bits.to_string());
    let gate = GateChip::<Fr>::default();
    let range = RangeChip::<Fr>::default(params.lookup_bits);
    let fp_chip = FpChip::<Fr>::new(&range, params.limb_bits, params.num_limbs);
    let ecc_chip = EccChip::new(&fp_chip);

    let ctx = builder.main(0);
    let revealed_evaluation = ctx.load_witness(proof.revealed_evaluation);
    
    let stage_proof = proof.stage_proof.
        iter().
        map(|proof| [ecc_chip.load_private(ctx, (proof[0].x, proof[0].y)), ecc_chip.load_private(ctx, (proof[1].x, proof[1].y))])
        .collect::<Vec<_>>();
    // process L, and R.

    let L = stage_proof.iter()
                        .map(|proof| proof[0].clone())
                        .collect::<Vec<_>>();
    let R = stage_proof.iter()
                        .map(|proof| proof[1].clone())
                        .collect::<Vec<_>>();
    let final_a = ctx.load_witness(proof.final_a);
    assigned_proof_of_inclusion {revealed_evaluation, L, R, final_a}
}


pub fn verify_batch_IPA_proof(
    builder: &mut GateThreadBuilder<Fr>,
    // params: &MSMCircuitParams,
    batched_IPA_proof: batch_IPA_proof,
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

    // obtain all of the inputs
    let commitments = &batched_IPA_proof.commitments.iter()
                                        .map(|commitment| 
                                        ecc_chip.load_private(ctx, (commitment.x, commitment.y)))
                                        .collect::<Vec<_>>();
    let vec_z = &batched_IPA_proof.vec_z.iter()
                            .map(|z| ctx.load_witness(*z))
                            .collect::<Vec<_>>();
    // let batched_proof = &batched_IPA_proof.batched_proof;
    // // let proofs_as_assigned_values = load_proof_of_inclusion(builder, batched_proof, make_public);
    // let commitment_to_weighted_poly = &batched_inclusion_proof.commitment_to_weighted_poly;
    // let commitment_to_weighted_poly = 
    //     ecc_chip.load_private(ctx, (commitment_to_weighted_poly.x,commitment_to_weighted_poly.y));
    
    // let list_of_proofs = &batched_inclusion_proof.list_of_proofs;
    // let list_of_proofs = list_of_proofs.iter()
    //                                     .map(|proof| load_proof_of_inclusion(builder, proof, make_public))
    //                                     .collect::<Vec<_>>();
    // let proof_of_weighted_poly = load_proof_of_inclusion(builder, &batched_inclusion_proof.proof_of_weighted_poly, make_public);
    // let g_init = &batched_IPA_proof.g_init.iter()
    //                     .map(|g| ecc_chip.load_private(ctx, (g.x, g.y)))
    //                     .collect::<Vec<_>>();
    // let U = ecc_chip.load_private(ctx, (batched_IPA_proof.U.x, batched_IPA_proof.U.y));

    

    // load all of the inputs
    

    unimplemented!()
}

fn main() {
    // std::env::set_var("RUST_BACKTRACE", "1");
    env_logger::init();

    let args = Cli::parse();
    let path = "examples/msm_circuit.config";
    let params: MSMCircuitParams = serde_json::from_reader(
        File::open(path).unwrap_or_else(|e| panic!("{path} does not exist: {e:?}")),
    )
    .unwrap();
    std::env::set_var("LOOKUP_BITS", params.lookup_bits.to_string());
    let private_inputs = test_ipa_export(3);
    // run_builder_on_inputs(verify_single_IPA_proof_hack, args, private_inputs);
    // let random_point = G1Affine::random(&mut OsRng);
    run_builder_on_inputs(verify_single_IPA_proof, args, private_inputs);

}




pub fn test_poseidon(builder: &mut GateThreadBuilder<Fr>,
    x: Fr,
    make_public: &mut Vec<AssignedValue<Fr>>){
        let ctx = builder.main(0);
        let gate = GateChip::<Fr>::default();
        // const T: usize = 3;
        // const RATE: usize = 2;
        // const R_F: usize = 8;
        // const R_P: usize = 33;
        //let mut hasher = Poseidon::<Fr, T, RATE>::new(R_F, R_P);
        let mut hasher = Poseidon::<Fr, Fr, T, RATE>::new::<R_F, R_P, 0>(&NativeLoader);
        let mut poseidon = PoseidonChip::<Fr, T, RATE>::new(ctx, R_F, R_P).unwrap();
        hasher.update(&[x]);
        let rust_output = hasher.squeeze();
        
        let x = ctx.load_witness(x);
        poseidon.update(&[x]);
        let circuit_output = poseidon.squeeze(ctx, &gate).unwrap();
        println!("The input is {:?}", x.value());
        println!("According to PoseidonChip, the value of output is {:?}", circuit_output.value());
        println!("According to rust, the value of the output is {:?}", rust_output);
    }


pub struct test_mul_input{
    points: [G1Affine;256],
    scalars: [Fr;256],
}

pub fn load_EC_point(
    builder: &mut GateThreadBuilder<Fr>,
    input: test_mul_input,
    make_public: &mut Vec<AssignedValue<Fr>>,
){
    let path = "examples/ipa_msm_circuit.config";
        let params: MSMCircuitParams = serde_json::from_reader(
            File::open(path).unwrap_or_else(|e| panic!("{path} does not exist: {e:?}")),
        )
        .unwrap();
        // set up chips.
        std::env::set_var("LOOKUP_BITS", params.lookup_bits.to_string());
        println!("lookup bits: {}", params.lookup_bits);
        let gate = GateChip::<Fr>::default();
        let range = RangeChip::<Fr>::default(params.lookup_bits);
        let fp_chip = FpChip::<Fr>::new(&range, params.limb_bits, params.num_limbs);
        let ecc_chip = EccChip::new(&fp_chip);
        let ctx = builder.main(0);
        
        let points = input.points;
        let scalars = input.scalars;
        let mut Hpoints = Vec::new();
        let mut Hscalars = Vec::new();
        for i in 0..256{
            Hscalars.push(vec![ctx.load_witness(scalars[i])]);
            Hpoints.push(ecc_chip.load_private(ctx, (points[i].x, points[i].y)));
        }
        let result = ecc_chip.variable_base_msm_in::<G1Affine>(
            builder, 
            &Hpoints,
            Hscalars,
            Fr::NUM_BITS as usize,
            4,
            0);
        
        println!("Hello world!!");
        // println!("The value of the result is {:?}", result.x());
}

