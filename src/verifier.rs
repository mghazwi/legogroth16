use crate::link::{PESubspaceSnark, SubspaceSnark};

use super::{PreparedVerifyingKey, Proof, VerifyingKey};

use ark_ec::pairing::Pairing;
use ark_relations::r1cs::{Result as R1CSResult, SynthesisError};

use ark_ec::AffineRepr;
use ark_ec::CurveGroup;

use ark_std::vec;
use ark_std::vec::Vec;
use core::ops::{AddAssign, Mul, Neg};

/// Prepare the verifying key `vk` for use in proof verification.
pub fn prepare_verifying_key<E: Pairing>(vk: &VerifyingKey<E>) -> PreparedVerifyingKey<E> {
    PreparedVerifyingKey {
        vk: vk.clone(),
        alpha_g1_beta_g2: E::pairing(vk.alpha_g1, vk.beta_g2).0,
        gamma_g2_neg_pc: vk.gamma_g2.into_group().neg().into().into(),
        delta_g2_neg_pc: vk.delta_g2.into_group().neg().into().into(),
    }
}

/// Verify a Groth16 proof `proof` against the prepared verification key `pvk`,
/// with respect to the instance `public_inputs`.
pub fn verify_proof<E: Pairing>(
    pvk: &PreparedVerifyingKey<E>,
    proof: &Proof<E>,
) -> R1CSResult<bool> {
    let commitments = vec![proof.link_d.into_group(), proof.d.into_group()];
    let link_verified = PESubspaceSnark::<E>::verify(
        &pvk.vk.link_pp,
        &pvk.vk.link_vk,
        &commitments
            .iter()
            .map(|p| p.into_affine())
            .collect::<Vec<_>>(),
        &proof.link_pi,
    );

    let qap = E::multi_miller_loop(
        [proof.a, proof.c, proof.d],
        [
            proof.b.into(),
            pvk.delta_g2_neg_pc.clone(),
            pvk.gamma_g2_neg_pc.clone(),
        ],
    );

    let test = E::final_exponentiation(qap).ok_or(SynthesisError::UnexpectedIdentity)?;

    Ok(link_verified && test.0 == pvk.alpha_g1_beta_g2)
}

pub fn verify_commitment<E: Pairing>(
    pvk: &PreparedVerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs: &[E::ScalarField],
    v: &E::ScalarField,
    link_v: &E::ScalarField,
) -> Result<bool, SynthesisError> {
    if (public_inputs.len() + 1) != pvk.vk.gamma_abc_g1.len() {
        return Err(SynthesisError::MalformedVerifyingKey);
    }
    if (public_inputs.len() + 2) != pvk.vk.link_bases.len() {
        return Err(SynthesisError::MalformedVerifyingKey);
    }

    let mut g_ic = pvk.vk.gamma_abc_g1[0].into_group();
    for (i, b) in public_inputs.iter().zip(pvk.vk.gamma_abc_g1.iter().skip(1)) {
        g_ic.add_assign(&b.mul(i));
    }
    g_ic.add_assign(&pvk.vk.eta_gamma_inv_g1.mul(v));

    let mut g_link = pvk.vk.link_bases[0].into_group();
    for (i, b) in public_inputs.iter().zip(pvk.vk.link_bases.iter().skip(1)) {
        g_link.add_assign(&b.mul(i));
    }
    g_link.add_assign(&pvk.vk.link_bases.last().unwrap().mul(link_v));

    Ok(proof.d == g_ic.into() && proof.link_d == g_link.into())
}
