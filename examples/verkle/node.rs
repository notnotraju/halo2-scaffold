use ff::{Field, PrimeField};
use halo2_base::{
    halo2_proofs::{
        halo2curves::{
            bn256::{Fr, G1Affine, Fq},
            group::Curve},
    },
    utils::{
        fe_to_biguint,
        biguint_to_fe,
    }
};
use fixed::NodeLink as NodeLink;

use num_traits::pow;

pub enum Node {
    Suffix(SuffixNode),
    Internal(InternalNode),
}
struct InternalNode {
    prefix: bytes32,
    children: Vec<NodeLink>,
}


