use core::ops::{Mul, Neg};

use crate::link::matrix::*;
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};

use ark_ff::{One, UniformRand};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

use ark_std::{marker::PhantomData, rand::Rng, vec, vec::Vec};

#[derive(Clone, Default, PartialEq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PP<
    G1: Clone + Default + CanonicalSerialize + CanonicalDeserialize,
    G2: Clone + Default + CanonicalSerialize + CanonicalDeserialize,
> {
    pub l: usize, // # of rows
    pub t: usize, // # of cols
    pub g1: G1,
    pub g2: G2,
}

impl<
        G1: Clone + Default + CanonicalSerialize + CanonicalDeserialize,
        G2: Clone + Default + CanonicalSerialize + CanonicalDeserialize,
    > PP<G1, G2>
{
    pub fn new(l: usize, t: usize, g1: &G1, g2: &G2) -> PP<G1, G2> {
        PP {
            l,
            t,
            g1: g1.clone(),
            g2: g2.clone(),
        }
    }
}

#[derive(Clone, Default, PartialEq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct EK<G1: Clone + Default + CanonicalSerialize + CanonicalDeserialize> {
    pub p: Vec<G1>,
}

#[derive(Clone, Default, PartialEq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct VK<G2: Clone + Default + CanonicalSerialize + CanonicalDeserialize> {
    pub c: Vec<G2>,
    pub a: G2,
}

pub trait SubspaceSnark {
    type KMtx;
    type InVec;
    type OutVec;

    type PP;

    type EK;
    type VK;

    type Proof;

    fn keygen<R: Rng>(rng: &mut R, pp: &Self::PP, m: Self::KMtx) -> (Self::EK, Self::VK);
    fn prove(pp: &Self::PP, ek: &Self::EK, x: &[Self::InVec]) -> Self::Proof;
    fn verify(pp: &Self::PP, vk: &Self::VK, y: &[Self::OutVec], pi: &Self::Proof) -> bool;
}

fn vec_to_g2<P: Pairing>(
    pp: &PP<P::G1Affine, P::G2Affine>,
    v: &Vec<P::ScalarField>,
) -> Vec<P::G2Affine> {
    v.iter()
        .map(|x| pp.g2.mul(*x).into_affine())
        .collect::<Vec<_>>()
}

pub struct PESubspaceSnark<PE: Pairing> {
    pairing_engine_type: PhantomData<PE>,
}

// NB: Now the system is for y = Mx
impl<P: Pairing> SubspaceSnark for PESubspaceSnark<P> {
    type KMtx = SparseMatrix<P::G1Affine>;
    type InVec = P::ScalarField;
    type OutVec = P::G1Affine;

    type PP = PP<P::G1Affine, P::G2Affine>;

    type EK = EK<P::G1Affine>;
    type VK = VK<P::G2Affine>;

    type Proof = P::G1Affine;

    fn keygen<R: Rng>(rng: &mut R, pp: &Self::PP, m: Self::KMtx) -> (Self::EK, Self::VK) {
        let mut k: Vec<P::ScalarField> = Vec::with_capacity(pp.l);
        for _ in 0..pp.l {
            k.push(P::ScalarField::rand(rng));
        }

        let a = P::ScalarField::rand(rng);

        let p = SparseLinAlgebra::<P>::sparse_vector_matrix_mult(&k, &m, pp.t);

        let c = scalar_vector_mult::<P>(&a, &k, pp.l);
        let ek = EK::<P::G1Affine> { p };
        let vk = VK::<P::G2Affine> {
            c: vec_to_g2::<P>(pp, &c),
            a: pp.g2.mul(a).into_affine(),
        };
        (ek, vk)
    }

    fn prove(pp: &Self::PP, ek: &Self::EK, x: &[Self::InVec]) -> Self::Proof {
        assert_eq!(pp.t, x.len());
        inner_product::<P>(x, &ek.p)
    }

    fn verify(pp: &Self::PP, vk: &Self::VK, y: &[Self::OutVec], pi: &Self::Proof) -> bool {
        assert_eq!(pp.l, y.len());

        // check that [x]1T · [C]2 = [π]1 · [a]2

        let mut g1_elements: Vec<<P as Pairing>::G1Prepared> = vec![];
        let mut g2_elements = vec![];

        for i in 0..y.len() {
            g1_elements.push(P::G1Prepared::from(y[i]));
            g2_elements.push(P::G2Prepared::from(vk.c[i]));
        }

        g1_elements.push(P::G1Prepared::from(*pi));
        g2_elements.push(P::G2Prepared::from(vk.a.into_group().neg().into_affine()));

        // take two references to element iterators instead of an iterator of tuples.
        P::TargetField::one() == P::multi_pairing(g1_elements, g2_elements).0
    }
}
