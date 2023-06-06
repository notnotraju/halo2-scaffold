// We still use Poseidon, but it is
// more of a fig leaf.
mod ipa_rust_clean;

use ipa_rust_clean::CompleteBatchIPAProof;
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
use serde::{Deserialize, Serialize};

type path: Vec<Vec<u8>>;

// write something to generate single VerkleTree proof.
pub struct SingleVerkleProof{
    pub commitment: G1Affine,
    pub key: Vec<u8>,
    pub path: path,
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
        value: u8,
    ) -> Self{
        let key_from_path:Vec<u8> = path.iter().fold(vec![], |mut acc, x| {
            acc.extend(x);
            acc
        });
        assert_eq!(key, key_from_path);
        let first_bytes = path.iter().map(|x| x[0]).collect::<Vec<u8>>();

        unimplemented!()
    }

}

fn main(){
    println!("Hello, world!");
}
