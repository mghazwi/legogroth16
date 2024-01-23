use core::ops::Mul;

use crate::{
    link::{PESubspaceSnark, SparseMatrix, SubspaceSnark, PP},
    r1cs_to_qap::R1CStoQAP,
    ProvingKey, Vec, VerifyingKey, ProvingKeyWithLink, VerifyingKeyWithLink, ProvingKeyCommon,
};
use ark_ec::{pairing::Pairing, scalar_mul::fixed_base::FixedBase, AffineRepr, CurveGroup};
use ark_ff::{Field, PrimeField, UniformRand, Zero};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, OptimizationGoal, Result as R1CSResult,
    SynthesisError, SynthesisMode,
};
use ark_std::rand::Rng;
use ark_std::{cfg_into_iter, cfg_iter, end_timer, start_timer};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Generates a random common reference string for
/// a circuit.
#[inline]
pub fn generate_random_parameters<E, C, R>(
    circuit: C,
    rng: &mut R,
) -> R1CSResult<ProvingKey<E>>
where
    E: Pairing,
    C: ConstraintSynthesizer<E::ScalarField>,
    R: Rng,
{

    let (alpha, beta, gamma, delta, eta) =
        generate_randomness::<E, R>(rng);

    let (pk, _) = generate_parameters::<E, C, R>(circuit, alpha, beta, gamma, delta, eta, rng).unwrap();
    Ok(pk)
}

/// Generates a random common reference string for
/// a circuit with CP-link.
#[inline]
pub fn generate_random_parameters_with_link<E, C, R>(
    circuit: C,
    pedersen_bases: &[E::G1Affine],
    rng: &mut R,
) -> R1CSResult<ProvingKeyWithLink<E>>
where
    E: Pairing,
    C: ConstraintSynthesizer<E::ScalarField>,
    R: Rng,
{

    let (alpha, beta, gamma, delta, eta) =
        generate_randomness::<E, R>(rng);

    let (groth16_pk, num_instance_variables) = generate_parameters::<E, C, R>(circuit, alpha, beta, gamma, delta, eta, rng).unwrap();


    let link_rows = 2; // we're comparirng two commitments
    let link_cols = pedersen_bases.len() + 1; // we have len witnesses and 1 hiding factor per row
    let link_pp = PP::<E::G1Affine, E::G2Affine> {
        l: link_rows,
        t: link_cols,
        g1: E::G1Affine::generator(),
        g2: E::G2Affine::generator(),
    };

    let mut link_m = SparseMatrix::<E::G1Affine>::new(link_rows, link_cols);
    let commit_witness_count = groth16_pk.vk.gamma_abc_g1[num_instance_variables..].len();
    link_m.insert_row_slice(0, 0, &pedersen_bases);
    link_m.insert_row_slice(
        1,
        0,
        &groth16_pk.vk.gamma_abc_g1[num_instance_variables..]
            .to_vec(),
    );
    link_m.insert_row_slice(1, commit_witness_count+1, &[groth16_pk.vk.eta_gamma_inv_g1]);

    let (link_ek, link_vk) = PESubspaceSnark::<E>::keygen(rng, &link_pp, link_m);
    let vk = VerifyingKeyWithLink::<E> {
        groth16_vk: groth16_pk.vk,
        link_pp,
        link_bases: pedersen_bases.to_vec(),
        link_vk,
    };

    Ok(ProvingKeyWithLink {
        vk,
        common: groth16_pk.common,
        link_ek,
    })
}

// generate random params
#[inline]
fn generate_randomness<E, R>(
    rng: &mut R,
) -> (
    E::ScalarField,
    E::ScalarField,
    E::ScalarField,
    E::ScalarField,
    E::ScalarField,
)
where
    E: Pairing,
    R: Rng,
{
    let alpha = E::ScalarField::rand(rng);
    let beta = E::ScalarField::rand(rng);
    let gamma = E::ScalarField::rand(rng);
    let delta = E::ScalarField::rand(rng);
    let eta = E::ScalarField::rand(rng);

    (alpha, beta, gamma, delta, eta)
}

/// Create parameters for a circuit, given some toxic waste.
pub fn generate_parameters<E, C, R>(
    circuit: C,
    alpha: E::ScalarField,
    beta: E::ScalarField,
    gamma: E::ScalarField,
    delta: E::ScalarField,
    eta: E::ScalarField,
    rng: &mut R,
) -> crate::Result<(ProvingKey<E>, usize)>
where
    E: Pairing,
    C: ConstraintSynthesizer<E::ScalarField>,
    R: Rng,
{
    type D<F> = GeneralEvaluationDomain<F>;

    let setup_time = start_timer!(|| "Groth16::Generator");
    let cs = ConstraintSystem::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    cs.set_mode(SynthesisMode::Setup);

    // Synthesize the circuit.
    let synthesis_time = start_timer!(|| "Constraint synthesis");
    circuit.generate_constraints(cs.clone())?;
    end_timer!(synthesis_time);

    let lc_time = start_timer!(|| "Inlining LCs");
    cs.finalize();
    end_timer!(lc_time);

    ///////////////////////////////////////////////////////////////////////////
    let domain_time = start_timer!(|| "Constructing evaluation domain");

    let domain_size = cs.num_constraints() + cs.num_instance_variables();
    let domain = D::new(domain_size).ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
    let t = domain.sample_element_outside_domain(rng);

    end_timer!(domain_time);
    ///////////////////////////////////////////////////////////////////////////

    let reduction_time = start_timer!(|| "R1CS to QAP Instance Map with Evaluation");
    // following line take into account the number of witness which will be included in the commitment
    let num_instance_var = cs.num_instance_variables();
    let num_instance_variables = num_instance_var + cs.num_witness_variables();
    let (a, b, c, zt, qap_num_variables, m_raw) =
        R1CStoQAP::instance_map_with_evaluation::<E::ScalarField, D<E::ScalarField>>(cs, &t)?;
    end_timer!(reduction_time);

    // Compute query densities
    let non_zero_a: usize = cfg_into_iter!(0..qap_num_variables)
        .map(|i| usize::from(!a[i].is_zero()))
        .sum();

    let non_zero_b: usize = cfg_into_iter!(0..qap_num_variables)
        .map(|i| usize::from(!b[i].is_zero()))
        .sum();

    // Cast to usize
    let scalar_bits = E::ScalarField::MODULUS_BIT_SIZE as usize;

    let gamma_inverse = gamma.inverse().ok_or(SynthesisError::UnexpectedIdentity)?;
    let delta_inverse = delta.inverse().ok_or(SynthesisError::UnexpectedIdentity)?;

    let gamma_abc = cfg_iter!(a[..num_instance_variables])
        .zip(&b[..num_instance_variables])
        .zip(&c[..num_instance_variables])
        .map(|((a, b), c)| (beta * a + &(alpha * b) + c) * &gamma_inverse)
        .collect::<Vec<_>>();

    let l = cfg_iter!(a)
        .zip(&b)
        .zip(&c)
        .map(|((a, b), c)| (beta * a + &(alpha * b) + c) * &delta_inverse)
        .collect::<Vec<_>>();

    drop(c);

    let g1_generator = E::G1::rand(rng);
    let g2_generator = E::G2::rand(rng);

    // Compute B window table
    let g2_time = start_timer!(|| "Compute G2 table");
    let g2_window = FixedBase::get_mul_window_size(non_zero_b);
    let g2_table = FixedBase::get_window_table::<E::G2>(scalar_bits, g2_window, g2_generator);
    end_timer!(g2_time);

    // Compute the B-query in G2
    let b_g2_time = start_timer!(|| "Calculate B G2");
    let b_g2_query = FixedBase::msm::<E::G2>(scalar_bits, g2_window, &g2_table, &b);
    drop(g2_table);
    end_timer!(b_g2_time);

    // Compute G window table
    let g1_window_time = start_timer!(|| "Compute G1 window table");
    let g1_window =
        FixedBase::get_mul_window_size(non_zero_a + non_zero_b + qap_num_variables + m_raw + 1);
    let g1_table = FixedBase::get_window_table::<E::G1>(scalar_bits, g1_window, g1_generator);
    end_timer!(g1_window_time);

    // Generate the R1CS proving key
    let proving_key_time = start_timer!(|| "Generate the R1CS proving key");

    let alpha_g1 = g1_generator.mul(alpha);
    let beta_g1 = g1_generator.mul(beta);
    let beta_g2 = g2_generator.mul(beta);
    let delta_g1 = g1_generator.mul(delta);
    let delta_g2 = g2_generator.mul(delta);

    // Compute the A-query
    let a_time = start_timer!(|| "Calculate A");
    let a_query = FixedBase::msm::<E::G1>(scalar_bits, g1_window, &g1_table, &a);
    drop(a);
    end_timer!(a_time);

    // Compute the B-query in G1
    let b_g1_time = start_timer!(|| "Calculate B G1");
    let b_g1_query = FixedBase::msm::<E::G1>(scalar_bits, g1_window, &g1_table, &b);
    drop(b);
    end_timer!(b_g1_time);

    // Compute the H-query
    let h_time = start_timer!(|| "Calculate H");
    let h_query = FixedBase::msm::<E::G1>(
        scalar_bits,
        g1_window,
        &g1_table,
        &cfg_into_iter!(0..m_raw - 1)
            .map(|i| zt * &delta_inverse * &t.pow([i as u64]))
            .collect::<Vec<_>>(),
    );

    end_timer!(h_time);

    // Compute the L-query
    let l_time = start_timer!(|| "Calculate L");
    let l_query = FixedBase::msm::<E::G1>(
        scalar_bits,
        g1_window,
        &g1_table,
        &l[num_instance_variables..],
    );
    drop(l);
    end_timer!(l_time);

    end_timer!(proving_key_time);

    // Generate R1CS verification key
    let verifying_key_time = start_timer!(|| "Generate the R1CS verification key");
    let gamma_g2 = g2_generator.mul(gamma);
    let gamma_abc_g1 = FixedBase::msm::<E::G1>(scalar_bits, g1_window, &g1_table, &gamma_abc);

    drop(g1_table);

    end_timer!(verifying_key_time);

    let eta_gamma_inv_g1 = g1_generator.mul(eta * &gamma_inverse);

    let vk = VerifyingKey::<E> {
        alpha_g1: alpha_g1.into_affine(),
        beta_g2: beta_g2.into_affine(),
        gamma_g2: gamma_g2.into_affine(),
        delta_g2: delta_g2.into_affine(),
        gamma_abc_g1: E::G1::normalize_batch(&gamma_abc_g1),
        eta_gamma_inv_g1: eta_gamma_inv_g1.into_affine(),
    };

    let batch_normalization_time = start_timer!(|| "Convert proving key elements to affine");
    let a_query = E::G1::normalize_batch(&a_query);
    let b_g1_query = E::G1::normalize_batch(&b_g1_query);
    let b_g2_query = E::G2::normalize_batch(&b_g2_query);
    let h_query = E::G1::normalize_batch(&h_query);
    let l_query = E::G1::normalize_batch(&l_query);
    end_timer!(batch_normalization_time);
    end_timer!(setup_time);

    let eta_delta_inv_g1 = g1_generator.mul(eta * &delta_inverse);

    let pk_common = ProvingKeyCommon {
        beta_g1: beta_g1.into_affine(),
        delta_g1: delta_g1.into_affine(),
        eta_delta_inv_g1: eta_delta_inv_g1.into_affine(),
        a_query,
        b_g1_query,
        b_g2_query,
        h_query,
        l_query,
    };

    Ok((ProvingKey {
        vk,
        common: pk_common,
    }, num_instance_var))
}
