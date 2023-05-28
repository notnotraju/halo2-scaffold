//! Example of scaffolding where function uses full `GateThreaderBuilder` instead of single `Context`

// mod binary_counting;
// mod ipa_rust_simple_hash_batch;
// // use crate::binary_counting::binary_counting;
// mod ipa_rust_clean;

#[allow(unused_imports)]
use ark_std::{start_timer, end_timer};
use axiom_eth::rlp::builder;
use binary_counting::{binary_counting_reverse, binary_counting_input};
use halo2_base::gates::range;
use halo2_base::halo2_proofs::plonk::Assigned;
use halo2_base::utils::bigint_to_fe;
use halo2_proofs::plonk::Circuit;
// use ipa_rust_simple_hash_batch::{proof_of_inclusion, single__IPA_proof, 
//                                 test_ipa_export, generate_hasher,
//                                 batch_IPA_proof};
use ipa_rust_clean::{ProofOfInclusion, CompleteSingleIPAProof, 
                    test_ipa_export, CompleteBatchIPAProof,
                test_batch_ipa_export};

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

pub fn fq_to_fr(
    ctx: &mut Context<Fr>,
    x: AssignedValue<Fq>
)-> AssignedValue<Fr>{
    
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
    std::env::set_var("DEGREE", 4.to_string());
    // run_builder_on_inputs(verify_single_IPA_proof_hack, args, private_inputs);
    // let random_point = G1Affine::random(&mut OsRng);
    //run_builder_on_inputs(verify_single_IPA_proof, args, private_inputs);
    // run_builder_on_inputs(verify_batch_IPA_proof, args, batch_private_inputs);
}


