#[allow(unused_imports)]
use ark_std::{start_timer, end_timer};
use axiom_eth::rlp::builder;

use halo2_base::gates::range;
use halo2_base::halo2_proofs::plonk::Assigned;
use halo2_base::utils::bigint_to_fe;
use halo2_proofs::plonk::Circuit;

use num_traits::pow;
use snark_verifier::loader::halo2::IntegerInstructions;
use snark_verifier::util::arithmetic::powers;
// use poseidon_rust::Poseidon;
use snark_verifier::util::hash::OptimizedPoseidonSpec as Spec;
use snark_verifier::util::hash::Poseidon as Poseidon;
use snark_verifier::loader::native::NativeLoader;

use axiom_eth::rlp::rlc::{RlcChip, RlcConfig,  FIRST_PHASE, RLC_PHASE};
use axiom_eth::rlp::builder::RlcThreadBuilder;
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
        RangeInstructions,
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
use std::env::var;
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

// okay, new setup.
// problem: I have a string stem, which is 31 bytes. I have a list
// of (non-empty) byte arrays a_i, and a list of their sizes s_i. I want to prove
// that a_1||...||a_n == stem, and that s_1 + ... + s_n = 31.
// if 
// should I enforce that sized_b has size n? In my example,
// that would be 31, and the last entries would somehow just be 0?
// moreover, each a_i has a non-empty first byte: b_i. ideally, we would
// enforce this via a_i = b_i || c_i, via RLC.
// here we may perhaps do this without.

pub struct Lengths<const n: usize>{
    pub lens: [usize; n],
}
pub struct FixedByteArraysInput<const n: usize>{
    pub s: [Fr; n],
    pub a: [[Fr; n];n], // list of n byte strings, each of length n.
    pub lengths: Lengths::<n>,
}

pub fn build_fixed_byte_array<const n: usize>()
-> FixedByteArraysInput<n>
{
    let mut s: [Fr; n] = 
        (0..n)
            .map(|x| Fr::from(x as u64))
            .collect::<Vec<Fr>>().try_into().unwrap();
    let a: [[Fr; n]; n] = 
        (0..n)
            .map(|x| {
                let mut answer = [Fr::zero(); n];
                answer[0] = Fr::from(x as u64);
                answer
            }
            )
            .collect::<Vec<[Fr; n]>>().try_into().unwrap();
    let lengths = Lengths::<n>{lens: [1; n]};
    FixedByteArraysInput::<n>{s, a, lengths}
    
}
// given a vector of bytes, and a length l, compute the corresponding field element.
// do range checks on all of the elements of bytes, to make sure they are in [0, 256)
pub fn bytes_to_field(
    ctx: &mut Context<Fr>,
    gate: &GateChip<Fr>,
    range: &RangeChip<Fr>,
    bytes: Vec<AssignedValue<Fr>>,
    l: usize
)-> AssignedValue<Fr>{
    let two_8 = Constant(Fr::from(2u64.pow(8)));
    let mut compute_field_element: Vec<AssignedValue<Fr>> =
         vec![ctx.load_constant(Fr::zero())];
    for i in 0..l{
        // range check that every entry is a byte
        range.range_check(ctx, bytes[i], 8); 
        let next_computation = 
            gate.mul_add(ctx,
                 compute_field_element[i],
                 two_8,
                 bytes[i]);
        compute_field_element.push(next_computation);
    }
    compute_field_element[l]
}

// helper function to feed into run_builder_on_inputs.
pub fn compute_bytes_to_field(
    builder: &mut GateThreadBuilder<Fr>,
    input: (Vec<Fr>, usize),
    make_public: &mut Vec<AssignedValue<Fr>>
){
    let ctx = builder.main(0);
    let gate = GateChip::<Fr>::default();
    let lookup_bits =
        var("LOOKUP_BITS").unwrap_or_else(|_| panic!("LOOKUP_BITS not set")).parse().unwrap();
    let range: RangeChip<Fr> = RangeChip::default(lookup_bits);
    let new_input =
        input.0.iter().map(|s| ctx.load_witness(*s))
        .collect::<Vec<AssignedValue<_>>>();
    let field_element = bytes_to_field(ctx, &gate, &range, new_input, input.1);
    println!("field element: {:?}", field_element);
    make_public.push(field_element);
}

// given an input of type FixedByteArraysInput::<n> (where n is the total length),
// i.e. a byte array s, and a list of byte arrays a_i, and a list of their sizes, check the concatenation
// condition: s == a_1 || ... || a_n.
// note: the list of their sizes is not in the circuit; it is pure rust, and this will be used to do fixed "shape"
// membership verification.
pub fn byte_concatenation<const n: usize>(
    builder: &mut GateThreadBuilder<Fr>,
    input: FixedByteArraysInput<n>,
    make_public: &mut Vec<AssignedValue<Fr>>
){
    assert!(n<32); // make sure there are fewer than 31 bytes.
    let ctx = builder.main(0);
    let gate = GateChip::<Fr>::default();
    let lookup_bits =
        var("LOOKUP_BITS").unwrap_or_else(|_| panic!("LOOKUP_BITS not set")).parse().unwrap();
    let range: RangeChip<Fr> = RangeChip::default(lookup_bits);
    // println!("input: s {:?}, a {:?}", input.s, input.a);
    let s: Vec<AssignedValue<Fr>> = input.s.iter().map(|s| ctx.load_witness(*s)).collect();
    // for each a_i, let f_i be the corresponding field element. 
    // we will compute weights w_i such that the concatenation has value: 
    // \sum f_i * w[i] (under the assumption that every element of a_i is a byte)
    // here we crucially use that the field has more than 31 bytes!
    let mut powers_of_256: Vec<Fr> = vec![];
    powers_of_256.push(Fr::one());
    powers_of_256.push(Fr::from(256u64));
    for i in 2..32{
        powers_of_256.push(powers_of_256[i-1]* powers_of_256[1]);
    }
    let mut weights: [Fr; n] = [Fr::zero(); n];
    weights[n-1] = Fr::one();
    for i in (0..(n-1)).rev(){
        weights[i] = powers_of_256[input.lengths.lens[i]]
                    * weights[i+1];
    }
    // the bottom is *fixed* for fixed n, lengths. (therefore, we do not need to write extra circuit
    // checks for it, we can simply declare it.)
    let weights = weights.iter()
        .map(|w| ctx.load_constant(*w))
        .collect::<Vec<_>>();
    // compute f_i:
    let mut f: [Fr; n] = [Fr::zero(); n];
    // turn inputs.a into a Vec<Vec<AssignedValue<Fr>>> in the obvious way.
    // implicitly do range checks on all of the bytes, to make sure they are in [0, 256) 
    let mut a = input.a.iter()
                    .map(|a| a.iter()
                        .map(|a_i|
                            ctx.load_witness(*a_i)) 
                        .collect::<Vec<_>>())
                        .collect::<Vec<_>>();      
    let lengths = input.lengths.lens;
    let a_field_elements = a.iter().enumerate()
            .map(|(i, a_i)|
        bytes_to_field(ctx, &gate, &range, a_i.clone(), lengths[i])).
        map(|val| {println!("{:?}", val.value()); 
        val}
        ).
        collect::<Vec<_>>();
    let s = input.s.iter().map(|s| ctx.load_witness(*s)).collect::<Vec<_>>();
    let s_as_field = 
        bytes_to_field(ctx, &gate, &range, s.clone(), n);
    println!("s_as_field: {:?}", s_as_field.value());
    let mut compute_concatenated_field_element: Vec<AssignedValue<Fr>> = vec![];
    compute_concatenated_field_element.push(gate.mul(ctx, a_field_elements[0], weights[0]));
    for i in 1..n{
        let next_computation = 
            gate.mul_add(ctx,
                 weights[i],
                 a_field_elements[i],
                 compute_concatenated_field_element[i-1]);
        compute_concatenated_field_element.push(next_computation);
    }
    let concatenated_field_element = compute_concatenated_field_element[n-1];
    println!("THe concatenated field element is: {:?}", concatenated_field_element.value());
    // assert_eq!(concatenated_field_element, s_as_field);
    let out = gate.is_equal(ctx, s_as_field, concatenated_field_element);
   println!("out: {:?}", out.value());
}


// what is problem? we have an s which is 31 bytes, and a
// list of vec_b, vec_size, where each b[i] is a byte array.
pub struct byte_array_concatenation_inputs{
    pub b: Vec<Fr>,
    pub vec_bytes: Vec<usize>,
    pub vec_sel: Vec<bool>,
    pub s: Fr,
    pub n: usize,
}
pub fn test_some_rlc(
    mut builder: RlcThreadBuilder<Fr>,
    input: [Fr; 32],
    len: usize,
){
    let ctx = builder.gate_builder.main(0);
    let inputs = ctx.assign_witnesses(input.clone());
    let len = ctx.load_witness(Fr::from(len as u64));  
}

// pub fn byte_array_concatenation(
//     ctx: &mut Context<Fr>,
//     input: byte_array_concatenation_inputs
// )-> AssignedValue<Fr>{
//     let gate = GateChip::<Fr>::default();
//     let (vec_b, vec_size): (Vec<_>, Vec<_>) =
//         input
//         .sized_b
//         .iter().map(|(b, size)|{ 
//             (ctx.load_witness(*b), ctx.load_witness(Fr::from(*size as u64)))}).unzip();
//     let s = ctx.load_witness(input.s);
//     let n = input.n;
//     let mut pow_of_2: Vec<AssignedValue<Fr>> = Vec::new();
//     pow_of_2.push(ctx.load_constant(Fr::one()));
//     for i in 1..n{
//         pow_of_2.push(gate.mul(ctx, pow_of_2[i-1], pow_of_2[0]));
//     }
//     // 2^8 is... 256, which is *more* than the number of the bits of the field.
//     // need to check that vec_b[i] is in the range [0, 2^{8* vec_size[i]}]

//     unimplemented!()
// }

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
    let vec_input = (0..8).map(|x| Fr::from(x as u64)).collect::<Vec<_>>();
    let mut input = [Fr::zero(); 8];
    for i in 0..8{
        input[i] = vec_input[i];
    }
    let array = build_fixed_byte_array::<5>();
    run_builder_on_inputs(byte_concatenation, args, array);
    // run_builder_on_inputs(compute_bytes_to_field, args, (vec_input, 8));
        // run_builder_on_inputs(verify_single_IPA_proof_hack, args, private_inputs);
    // let random_point = G1Affine::random(&mut OsRng);
    //run_builder_on_inputs(verify_single_IPA_proof, args, private_inputs);
    // run_builder_on_inputs(verify_batch_IPA_proof, args, batch_private_inputs);
}


