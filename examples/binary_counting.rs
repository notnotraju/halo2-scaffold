#![feature(trait_alias)]
use ark_std::{start_timer, end_timer};
use clap::Parser;
// halo2_ecc
use halo2_ecc::{
    fields::{FpStrategy, FieldChip},
    ecc::{
        EccChip, EcPoint},
        bn254::FpChip,
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
            bn256::{Fr, G1Affine, Fq},
            group::Curve},
        plonk::{ConstraintSystem, Error},
        
    },
    utils::{
        fs::gen_srs,
        fe_to_biguint,
        fe_to_bigint,
        biguint_to_fe,
        bigint_to_fe,
        ScalarField,
        BigPrimeField
    }
};

use halo2_scaffold::scaffold::{cmd::Cli, run, run_builder_on_inputs};

// use ff::{PrimeField};
// use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};
// use std::{
//     fs::{self, File},
//     io::{BufRead, BufReader},
// };
// #[derive(Clone, Debug, Serialize, Deserialize)]
// pub struct binary_counting_input<F: ScalarField> {
//     field_elts: [F; 4],
// }

// pub fn binary_counting<F: ScalarField>(
//     ctx: &mut Context<F>,
//     gate: &GateChip<F>,
//     input: binary_counting_input<F>,
//     make_public: &mut Vec<AssignedValue<F>>)-> Vec<AssignedValue<F>> {
//     // let gate = GateChip::<F>::default();
//     let mut input_values: Vec<AssignedValue<F>>= Vec::new();
//     let k = input.field_elts.len();
//     for _ in 0..k {
//         input_values = 
//             input.field_elts.iter()
//                 .map(|x| 
//                     ctx.load_witness(*x))
//                 .collect();
//     }
    
//     let mut output_values: Vec<AssignedValue<F>>= Vec::new();
//     let truncated_product = 
//         input_values.
//         iter().
//         fold(Constant(F::one()), |acc, x|
//         halo2_base::QuantumCell::Existing(gate.mul(ctx, acc, *x)));
    
//     // s_0 is the product of the inverses of the inputs
//     output_values.push(gate.div_unsafe(ctx, Constant(F::one()), truncated_product));
    
//     let mut square_inputs: Vec<AssignedValue<F>>= Vec::new();
//     for i in 0..k {
//         square_inputs.push(gate.mul(ctx, input_values[i], input_values[i]));
//     }

//     for i in 1.. (2_i32).pow(k as u32) {
//         let e = (i as f32).log2().floor() as u32;
//         let max_bit = (2_u32).pow(e);
//         let lower_order_bits = i - (max_bit as i32);
//         output_values.push(gate.mul(ctx,
//                                      output_values[lower_order_bits as usize], 
//                                      square_inputs[e as usize]));
//     }
//     output_values
//     // println!("output_values: {:?}", output_values);
// }


// build code that takes in assigned values rather than field elements.
// NOTE: must pass in a clone!! otherwise I think I lose things?
#[derive(Clone, Debug)]
pub struct binary_counting_input<F: ScalarField> {
    pub field_elts: Vec<AssignedValue<F>>,
}
// input is <w_1,...,w_k> (AssignedValue<F>)
// output is <w_1^{-1}*...*w_k^{-1}, w^1*w_2^{-1}*...*w_k^{-1}, w_1*w_2^{-1}*...*w_k^{-1}, ... w_1*w_2*...*w_k>
// k = 2, <w_1, w_2>
// output: <w_1^{-1}*w_2^{-1}, w_1*w_2^{-1}, w_1^{-1}*w_2, w_1*w_2>
// 00, 10, 01, 11 (i.e., reverse each string, e.g. 110000 -> 000011)
// 0 ,  1,  2,  3
pub fn binary_counting<F: ScalarField>(
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    input: binary_counting_input<F>,
    // make_public: &mut Vec<AssignedValue<F>>
    )-> Vec<AssignedValue<F>> {

    let input_values = input.field_elts;
    let k = input_values.len();
 
    let mut output_values: Vec<AssignedValue<F>>= Vec::new();
    // multiply all of the values of the input.
    let truncated_product = 
        input_values.
        iter().
        fold(Constant(F::one()), |acc, x|
        halo2_base::QuantumCell::Existing(gate.mul(ctx, acc, *x)));
    
    // s_0 is the product of the inverses of the inputs
    output_values.push(gate.div_unsafe(ctx, Constant(F::one()), truncated_product));
    
    let mut square_inputs: Vec<AssignedValue<F>>= Vec::new();
    for i in 0..k {
        square_inputs.push(gate.mul(ctx, input_values[i], input_values[i]));
    }
    // build the vector.
    for i in 1.. (2_i32).pow(k as u32) {
        let e = (i as f32).log2().floor() as u32;
        let max_bit = (2_u32).pow(e);
        let lower_order_bits = i - (max_bit as i32);
        output_values.push(gate.mul(ctx,
                                     output_values[lower_order_bits as usize], 
                                     square_inputs[e as usize]));
    }
    // println!("output_values: {:?}", output_values);
    output_values
    
}

// build *reverse* binary counting pattern. This reverses the input.
pub fn binary_counting_reverse<F: ScalarField>(
    ctx: &mut Context<F>,
    gate: &GateChip<F>,
    input: binary_counting_input<F>,
    // make_public: &mut Vec<AssignedValue<F>>
    )-> Vec<AssignedValue<F>> {

    let input_values = input.field_elts
                .iter()
                .rev()
                .collect::<Vec<_>>();
    let k = input_values.len();
 
    let mut output_values: Vec<AssignedValue<F>>= Vec::new();
    let truncated_product = 
        input_values.
        iter().
        fold(Constant(F::one()), |acc, x|
        halo2_base::QuantumCell::Existing(gate.mul(ctx, acc, **x)));
    
    // s_0 is the product of the inverses of the inputs
    output_values.push(gate.div_unsafe(ctx, Constant(F::one()), truncated_product));
    
    let mut square_inputs: Vec<AssignedValue<F>>= Vec::new();
    for i in 0..k {
        square_inputs.push(gate.mul(ctx, *input_values[i], *input_values[i]));
    }

    for i in 1.. (2_i32).pow(k as u32) {
        let e = (i as f32).log2().floor() as u32;
        let max_bit = (2_u32).pow(e);
        let lower_order_bits = i - (max_bit as i32);
        output_values.push(gate.mul(ctx,
                                     output_values[lower_order_bits as usize], 
                                     square_inputs[e as usize]));
    }
    output_values
    // println!("output_values: {:?}", output_values);
}
// built to test the binary counting circuit
pub fn compute_binary_counting<F:ScalarField>(
    builder: &mut GateThreadBuilder<F>,
    input: Vec<F>,
    make_public: &mut Vec<AssignedValue<F>>) {
        let ctx = builder.main(0);
        let gate = GateChip::<F>::default();
        let input = binary_counting_input::<F> {
            field_elts: input.iter().map(|x| ctx.load_witness(*x)).collect::<Vec<_>>(),
        };
        // choose between binary_counting and its reverse.
        let output_values = binary_counting_reverse(ctx, &gate, input);
        // let output_values = binary_counting(ctx, &gate, input);
        // println!("output_values: {:?}", output_values);
        for out in output_values.iter() {
            make_public.push(*out);
        }
    }







fn main() {
    env_logger::init();
    std::env::set_var("RUST_BACKTRACE", "1");
    let args = Cli::parse();
    // let mut make_public = Vec::new();
    let private_inputs =
        (1..9 as u64)
        .map(|x| Fr::from(x))
        .collect::<Vec<_>>();
    run_builder_on_inputs(compute_binary_counting, args, private_inputs);
}