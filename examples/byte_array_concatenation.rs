//! Example of scaffolding where function uses full `GateThreaderBuilder` instead of single `Context`

// mod binary_counting;
// mod ipa_rust_simple_hash_batch;
// // use crate::binary_counting::binary_counting;
// mod ipa_rust_clean;

#[allow(unused_imports)]
use ark_std::{start_timer, end_timer};
use axiom_eth::rlp::builder;

use halo2_base::gates::range;
use halo2_base::halo2_proofs::plonk::Assigned;
use halo2_base::utils::bigint_to_fe;
use halo2_proofs::plonk::Circuit;

use num_traits::pow;
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
// should I enforce that sized_b has size n? In my example,
// that would be 31, and the last entries would somehow just be 0?


// what is problem? we have an s which is 31 bytes, and a
// list of vec_b, vec_size, where each b[i] is a byte array.
pub struct byte_array_concatenation_inputs{
    pub sized_b: Vec<(Fr, usize)>,
    pub vec_bytes: Vec<usize>,
    pub vec_sel: Vec<bool>,
    pub s: Fr,
    pub n: usize,
}

pub fn byte_array_concatenation(
    ctx: &mut Context<Fr>,
    input: byte_array_concatenation_inputs
)-> AssignedValue<Fr>{
    let gate = GateChip::<Fr>::default();
    let (vec_b, vec_size): (Vec<_>, Vec<_>) =
        input
        .sized_b
        .iter().map(|(b, size)|{ 
            (ctx.load_witness(*b), ctx.load_witness(Fr::from(*size as u64)))}).unzip();
    let s = ctx.load_witness(input.s);
    let n = input.n;
    let mut pow_of_2: Vec<AssignedValue<Fr>> = Vec::new();
    pow_of_2.push(ctx.load_constant(Fr::one()));
    for i in 1..n{
        pow_of_2.push(gate.mul(ctx, pow_of_2[i-1], pow_of_2[0]));
    }
    // 2^8 is... 256, which is *more* than the number of the bits of the field.
    // need to check that vec_b[i] is in the range [0, 2^{8* vec_size[i]}]

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


