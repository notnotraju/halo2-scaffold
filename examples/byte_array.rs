use axiom_eth::{
    keccak::KeccakChip,
    util::{bytes_be_to_u128, uint_to_bytes_be},
    EthChip, Field,
};
use clap::Parser;
use halo2_base::{gates::RangeInstructions, AssignedValue, Context};
use halo2_scaffold::scaffold::{cmd::Cli, run_eth};
use serde::{Deserialize, Serialize};

// GIVEN: a byte array s of length n (max 31)
// a list of byte strings a_0,...,a_{n-1}
// maybe a list of sizes l_0,...,l_{n-1}
// such that l_i is the length of a_i, and l_0 + ... + l_{n-1} = n
// and s == a_0||...|| a_{n-1}

// this should be done by constrain_rlc_concat!
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ConcatInput<F: Field, const N: usize> {
    pub s: Vec<F>,
    pub a: Vec<Vec<F>>,
    pub l: Vec<F>,
}
pub fn check_concat<F: Field, const N: usize> (
    ctx: &mut Context<F>,
    eth_chip: &EthChip<F>,
    keccak: &mut KeccakChip<F>,
    input: ConcatInput<F, N>,
    make_public: &mut Vec<AssignedValue<F>>,
) -> impl FnOnce(&mut Context<F>, &mut Context<F>, &EthChip<F>) + Clone {
    let range = eth_chip.range();
    let gate = range.gate();
    let s = input.s.iter().map(|x| ctx.load_witness(*x)).collect::<Vec<_>>();
    let a = input.a.iter().map(|x| x.iter().map(|y| ctx.load_witness(*y)).collect::<Vec<_>>()).collect::<Vec<_>>();
    let l = input.l.iter().map(|x| ctx.load_witness(*x)).collect::<Vec<_>>();
    // check the sum of the lengths == n!!
    let n = ctx.load_constant(F::from(N as u64));

    let callback =
        |ctx_gate: &mut Context<F>, ctx_rlc: &mut Context<F>, eth_chip: &EthChip<F>| {
            let rlc_chip = eth_chip.rlc();
            let num_frags = N;
            // compute the rlc of s.
            let rlc_s = rlc_chip.compute_rlc(
                (ctx_gate, ctx_rlc),
                gate,
                s.clone(),
                n
            );
            // compute the vector of rlcs of the a[i].
            // note that here the lengths are super important!
            let rlc_a = 
                a.iter().zip(l.iter()).
                map(|(x, l_i)| 
                    rlc_chip.compute_rlc(
                    (ctx_gate, ctx_rlc),
                    gate,
                    x.clone(),
                    l_i.clone()
                )).collect::<Vec<_>>();
            // again, our goal is to use the rlc_concat_var method.
            // to do this, we need to show that 
            let constrain_inputs = 
                a.iter().zip(l.iter()).
                map(|(x, l_i)| 
                    (x.clone(), l_i.clone(), N)
                ).
                collect::<Vec<_>>();
            rlc_chip.constrain_rlc_concat_var(
                ctx_gate,
                gate, 
                inputs,
                _,
                num_frags)
        };

    callback
}


#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CircuitInput {
    pub bytes31: String, // 1 field elements, but as strings for easier deserialization
}

// Input is a single field element `bytes31` representing `31` bytes. We decompose the field eleemnt in big endian into 31 bytes
// Then we compute keccak hash of the 31 bytes and output the hash as two field elements in hi-lo (u128, u128) form
// @dev `F` must be `axiom_eth::Field` instead of `ScalarField` for some technical reasons
fn compute_keccak_bytes31<F: Field>(
    ctx: &mut Context<F>,
    eth_chip: &EthChip<F>,
    keccak: &mut KeccakChip<F>,
    inp: CircuitInput,
    make_public: &mut Vec<AssignedValue<F>>,
) -> impl FnOnce(&mut Context<F>, &mut Context<F>, &EthChip<F>) + Clone {
    // the output is a callback function, just take this trait for granted

    // load the input
    let x = ctx.load_witness(F::from_str_vartime(&inp.bytes31).unwrap());
    make_public.push(x);

    // x is a single field element, which can fit up to ~254 bits

    // `EthChip` contains `RangeChip`, `Gate`
    let range = eth_chip.range();
    // we decompose x into 31 bytes, axiom-eth has a function for this
    let bytes = uint_to_bytes_be(ctx, range, &x, 31);

    let hash_idx = keccak.keccak_fixed_len(ctx, range.gate(), bytes, None);
    // this only returns an index of the output in some "keccak table" (mostly for technical reasons)
    // to get the value, we have to fetch:
    let out_bytes32 = keccak.fixed_len_queries[hash_idx].output_assigned.clone();
    let out_hilo = bytes_be_to_u128(ctx, range.gate(), &out_bytes32);
    assert_eq!(out_hilo.len(), 2);
    for o in out_hilo {
        make_public.push(o);
    }

    // Just for display purposes, print the output as byte string:
    print!("Output: ");
    for b in out_bytes32 {
        print!("{:02x}", b.value().get_lower_32() as u8);
    }
    println!();

    // Here's the tricky part: you MUST provide a callback function (as a closure) for what to do in SecondPhase of the Challenge API
    // This includes any function that requires using the random challenge value

    // For Keccak, this function is empty because we fill it in for you behind the scenes
    let callback =
        |_ctx_gate: &mut Context<F>, _ctx_rlc: &mut Context<F>, _eth_chip: &EthChip<F>| {};

    callback
}

fn main() {
    env_logger::init();

    let args = Cli::parse();
    // use run_eth instead of run
    run_eth(compute_keccak_bytes31, args);
}