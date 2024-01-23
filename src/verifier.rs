use crate::{VerifyingKeyWithLink, ProofWithLink};
use crate::link::{PESubspaceSnark, SubspaceSnark};
use ark_ff::{One, PrimeField};
use super::{PreparedVerifyingKey, Proof, VerifyingKey};

use ark_ec::{
    pairing::Pairing,AffineRepr, CurveGroup,
    VariableBaseMSM,
};
use ark_relations::r1cs::{Result as R1CSResult, SynthesisError};

use ark_std::{
    cfg_iter,
    vec,
    vec::Vec,
};
use core::ops::{AddAssign, Neg};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Prepare the verifying key `vk` for use in proof verification.
pub fn prepare_verifying_key<E: Pairing>(vk: &VerifyingKey<E>) -> PreparedVerifyingKey<E> {
    PreparedVerifyingKey {
        vk: vk.clone(),
        alpha_g1_beta_g2: E::pairing(vk.alpha_g1, vk.beta_g2).0,
        gamma_g2_neg_pc: vk.gamma_g2.into_group().neg().into().into(),
        delta_g2_neg_pc: vk.delta_g2.into_group().neg().into().into(),
    }
}

/// Prepare proof inputs for use with [`verify_proof_with_prepared_inputs`], wrt the prepared
/// verification key `pvk` and instance public inputs.
pub fn prepare_inputs<E: Pairing>(
    pvk: &PreparedVerifyingKey<E>,
    public_inputs: &[E::ScalarField],
) -> crate::Result<E::G1> {
    if (public_inputs.len() + 1) > pvk.vk.gamma_abc_g1.len() {
        return Err(SynthesisError::MalformedVerifyingKey).map_err(|e| e.into());
    }

    if public_inputs.len() > 2 {
        let mut inp = Vec::with_capacity(1 + public_inputs.len());
        inp.push(E::ScalarField::one());
        inp.extend_from_slice(public_inputs);
        let inp = cfg_iter!(inp).map(|a| a.into_bigint()).collect::<Vec<_>>();
        Ok(E::G1::msm_bigint(&pvk.vk.gamma_abc_g1, &inp))
    } else {
        let mut d = pvk.vk.gamma_abc_g1[0].into_group();
        for (i, b) in public_inputs.iter().zip(pvk.vk.gamma_abc_g1.iter().skip(1)) {
            d.add_assign(&b.mul_bigint(i.into_bigint()));
        }
        Ok(d)
    }
}

/// Verify the groth16 proof and the the Subspace Snark on the equality of openings of cp_link and proof.d
pub fn verify_proof_with_link<E: Pairing>(
    pvk: &PreparedVerifyingKey<E>,
    vk: &VerifyingKeyWithLink<E>,
    proof: &ProofWithLink<E>,
    public_inputs: &[E::ScalarField],
) -> R1CSResult<bool> {
    let proof_verified = verify_proof(
        pvk,
        &proof.groth16_proof,
        public_inputs,
    )?;
    let commitments = vec![proof.link_d.clone(), proof.groth16_proof.d.clone()];
    let link_verified = PESubspaceSnark::<E>::verify(&vk.link_pp, &vk.link_vk, &commitments, &proof.link_pi);
    Ok(proof_verified && link_verified)
}

/// Verify a LegoGroth16 proof `proof` against the prepared verification key `pvk`
pub fn verify_proof<E: Pairing>(
    pvk: &PreparedVerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs: &[E::ScalarField],
) -> R1CSResult<bool> {
    verify_groth16_proof(
        pvk,
        proof.a,
        proof.b,
        proof.c,
        calculate_d(pvk, proof, public_inputs).unwrap(),
    )
}

/// Verify a Groth16 proof [a,b,c,d] against the prepared verification key `pvk`
pub fn verify_groth16_proof<E: Pairing>(
    pvk: &PreparedVerifyingKey<E>,
    a: E::G1Affine,
    b: E::G2Affine,
    c: E::G1Affine,
    d: E::G1Affine,
) -> R1CSResult<bool> {

    let qap = E::multi_miller_loop(
        [a, c, d],
        [
            b.into(),
            pvk.delta_g2_neg_pc.clone(),
            pvk.gamma_g2_neg_pc.clone(),
        ],
    );

    let test = E::final_exponentiation(qap).ok_or(SynthesisError::UnexpectedIdentity)?;

    Ok(test.0 == pvk.alpha_g1_beta_g2)
}

pub fn calculate_d<E: Pairing>(
    pvk: &PreparedVerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs: &[E::ScalarField],
) -> crate::Result<E::G1Affine> {
    let mut d = prepare_inputs(pvk, public_inputs)?;
    d += proof.d;
    Ok(d.into_affine())
}

// this function checks that the commitments in the proof open to the witnesses
// but with different bases and randomness. 
// This function should only be called by the prover, the verifier does not
// know `witnesses_expected_in_commitment` or `link_v`.

pub fn verify_commitments<E: Pairing>(
    vk: &VerifyingKeyWithLink<E>,
    proof: &ProofWithLink<E>,
    public_inputs_count: usize,
    witnesses_expected_in_commitment: &[E::ScalarField],
    v: &E::ScalarField,
    link_v: &E::ScalarField,
) -> Result<bool, SynthesisError>{
    verify_link_commitment::<E>(
        &vk.link_bases,
        &proof.link_d,
        witnesses_expected_in_commitment,
        link_v,
    )?;
    verify_witness_commitment::<E>(
        &vk.groth16_vk,
        &proof.groth16_proof,
        public_inputs_count,
        witnesses_expected_in_commitment,
        v,
    )
}

/// Check the opening of cp_link.
pub fn verify_link_commitment<E: Pairing>(
    cp_link_bases: &[E::G1Affine],
    link_d: &E::G1Affine,
    witnesses_expected_in_commitment: &[E::ScalarField],
    link_v: &E::ScalarField,
) -> Result<bool, SynthesisError>{
    // Some witnesses are committed in `link_d` with randomness `link_v`
    if (witnesses_expected_in_commitment.len() + 1) > cp_link_bases.len() {
        return Err(SynthesisError::MalformedVerifyingKey);
    }
    let mut committed = cfg_iter!(witnesses_expected_in_commitment)
        .map(|p| p.into_bigint())
        .collect::<Vec<_>>();
    committed.push(link_v.into_bigint());

    if *link_d != E::G1::msm_bigint(cp_link_bases, &committed).into_affine() {
        return Err(SynthesisError::MalformedVerifyingKey);
    }
    Ok(true)
}

/// Given the proof, verify that the commitment in it (`proof.d`) commits to the witness.
pub fn verify_witness_commitment<E: Pairing>(
    vk: &VerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs_count: usize,
    witnesses_expected_in_commitment: &[E::ScalarField],
    v: &E::ScalarField,
) -> Result<bool, SynthesisError> {
    // Some witnesses are also committed in `proof.d` with randomness `v`
    if (public_inputs_count + witnesses_expected_in_commitment.len() + 1) > vk.gamma_abc_g1.len() {
        return Err(SynthesisError::MalformedVerifyingKey);
    }
    let committed = cfg_iter!(witnesses_expected_in_commitment)
        .map(|p| p.into_bigint())
        .collect::<Vec<_>>();

    // Check that proof.d is correctly constructed.
    let mut d = E::G1::msm_bigint(
        &vk.gamma_abc_g1[1 + public_inputs_count..1 + public_inputs_count + committed.len()],
        &committed,
    );
    d.add_assign(&vk.eta_gamma_inv_g1.mul_bigint(v.into_bigint()));

    if proof.d != d.into_affine() {
        return Err(SynthesisError::MalformedVerifyingKey);
    }

    Ok(true)
}