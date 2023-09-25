#![allow(non_snake_case)]
use crate::polynomial::Polynomial;
use crate::transcript::Transcript;
use crate::{define_add_variants, define_mul_variants};
use blstrs::*;
use ff::Field;
use group::prime::PrimeCurveAffine;
use group::Curve;
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;
use std::ops::{Add, Mul, Neg};
use serde::Deserialize;
use serde::Serialize;

#[derive(Debug)]
pub struct Kzg10<const MAX_GATES: usize> {
    pub powers_x_g1: [G1Affine; MAX_GATES], // This will have as size the max number of gates allowed.
    pub powers_x_g2: [G2Affine; 2],         // we only have power 0 and 1
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Kzg10Commitment(pub(crate) G1Affine);

pub struct Kzg10BatchProof(Kzg10Commitment, Kzg10Commitment);

impl<const MAX_GATES: usize> Kzg10<MAX_GATES> {
    pub fn setup() -> Self {
        let toxic_waste = Scalar::random(&mut ChaCha20Rng::from_seed([0u8; 32]));
        let mut powers_x_g1 = [G1Affine::default(); MAX_GATES];
        let mut powers_x_g2 = [G2Affine::default(); 2];

        powers_x_g2[0] = G2Affine::generator();
        powers_x_g2[1] = (G2Affine::generator() * toxic_waste).to_affine();

        let mut temp_g1 = G1Affine::generator();

        for powers in powers_x_g1.iter_mut() {
            *powers = temp_g1;
            temp_g1 = (temp_g1 * toxic_waste).to_affine(); // Doing unnecessary addition at last iteration, who cares?
        }

        Self {
            powers_x_g1,
            powers_x_g2,
        }
    }

    pub fn commit(&self, polynomial: &Polynomial) -> Kzg10Commitment {
        assert!(
            polynomial.0.len() <= MAX_GATES,
            "Polynomial degree not supported"
        );
        let mut commitment = G1Affine::identity();
        for (srs, coefficient) in self.powers_x_g1.iter().zip(polynomial.0.iter()) {
            commitment = (commitment + srs * coefficient).to_affine();
        }

        Kzg10Commitment(commitment)
    }

    /// We simplify this function as is described in the paper. The open protocol for multiple evaluation points assumes
    /// that there are only two distinct evaluation points.
    #[allow(clippy::too_many_arguments)]
    pub fn batch_prove(
        &self,
        polynomials_a: &[Polynomial],
        polynomials_b: &[Polynomial],
        commitments_a: &[Kzg10Commitment],
        commitments_b: &[Kzg10Commitment],
        eval_a: &Scalar,
        eval_b: &Scalar,
        output_a: &[Scalar],
        output_b: &[Scalar],
        transcript: &mut Transcript,
    ) -> Kzg10BatchProof {
        assert!(
            polynomials_a.iter().any(|poly| poly.0.len() <= MAX_GATES),
            "Polynomial degree not supported"
        );
        assert!(
            polynomials_b.iter().any(|poly| poly.0.len() <= MAX_GATES),
            "Polynomial degree not supported"
        );

        let len_a = commitments_a.len();
        let len_b = commitments_b.len();
        // First we use the transcript to generate two scalars.
        // The code here will panic if not all vectors are the same, but that's fine here,
        // as we really need to enforce that.
        // NOTE: This is also insecure. In a real-world scenario we would need to change the label of each
        // commitment. But it is a bit of a pain to do (see here ark-plonk/somewhere).
        transcript.append_scalar(b"eval group 1", eval_a);
        for i in 0..len_a {
            transcript.append_point(b"commitments group 1", &commitments_a[i].0);
            transcript.append_scalar(b"output group 1", &output_a[i]);
        }

        transcript.append_scalar(b"eval group 1", eval_b);
        for j in 0..len_b {
            transcript.append_point(b"commitments group 1", &commitments_b[j].0);
            transcript.append_scalar(b"output group 1", &output_b[j]);
        }

        let gamma = transcript.challenge_scalar(b"gamma");
        let gammaprime = transcript.challenge_scalar(b"gammaprime");

        // Now we compute h(X) and h'(X) polynomials
        let mut h_x = Polynomial::zero(MAX_GATES);
        let mut gamma_powers = Scalar::one();
        for poly in polynomials_a {
            let mut temp_poly = poly.clone();
            // we subtract the polynomial evaluated at the evaluation point
            temp_poly.0[0] -= poly.eval(eval_a);
            // we divide by the monomial X - eval_a
            let poly_division = temp_poly / Polynomial(vec![eval_a.neg(), Scalar::one()]);
            h_x += &poly_division * gamma_powers;
            gamma_powers *= gamma;
        }

        let mut h_prime_x = Polynomial::zero(MAX_GATES);

        let mut gammaprime_powers = Scalar::one();
        for poly in polynomials_b {
            let mut temp_poly = poly.clone();
            // we subtract the polynomial evaluated at the evaluation point
            temp_poly.0[0] -= poly.eval(eval_b);
            // we divide by the monomial X - eval_b
            let poly_division = temp_poly / Polynomial(vec![eval_b.neg(), Scalar::one()]);
            h_prime_x += &poly_division * gammaprime_powers;

            // we update the power of gamma
            gammaprime_powers *= gammaprime;
        }

        Kzg10BatchProof(self.commit(&h_x), self.commit(&h_prime_x))
    }

    /// We simplify this function as is described in the paper. The open protocol for multiple evaluation points assumes
    /// that there are only two distinct evaluation points.
    #[allow(clippy::too_many_arguments)]
    pub fn batch_verify(
        &self,
        proof: &Kzg10BatchProof,
        commitments_a: &[Kzg10Commitment],
        commitments_b: &[Kzg10Commitment],
        eval_a: &Scalar,
        eval_b: &Scalar,
        output_a: &[Scalar],
        output_b: &[Scalar],
        transcript: &mut Transcript,
    ) -> Result<(), ()> {
        let len_a = commitments_a.len();
        let len_b = commitments_b.len();
        // First we use the transcript to generate two scalars.
        // The code here will panic if not all vectors are the same, but that's fine here,
        // as we really need to enforce that.
        // NOTE: This is also insecure. In a real-world scenario we would need to change the label of each
        // commitment. But it is a bit of a pain to do (see here ark-plonk/somewhere).
        transcript.append_scalar(b"eval group 1", eval_a);
        for i in 0..len_a {
            transcript.append_point(b"commitments group 1", &commitments_a[i].0);
            transcript.append_scalar(b"output group 1", &output_a[i]);
        }

        transcript.append_scalar(b"eval group 1", eval_b);
        for j in 0..len_b {
            transcript.append_point(b"commitments group 1", &commitments_b[j].0);
            transcript.append_scalar(b"output group 1", &output_b[j]);
        }

        let gamma = transcript.challenge_scalar(b"gamma");
        let gammaprime = transcript.challenge_scalar(b"gammaprime");

        let rprime = transcript.challenge_scalar(b"rprime");

        let mut F = G1Affine::identity();

        let mut gamma_powers = Scalar::one();
        for i in 0..len_a {
            F = (F + commitments_a[i].0 * gamma_powers
                - G1Affine::generator() * (gamma_powers * output_a[i]))
                .to_affine();
            gamma_powers *= gamma;
        }

        let mut gammaprime_powers = Scalar::one();
        for j in 0..len_b {
            F = (F + commitments_b[j].0 * (rprime * gammaprime_powers)
                - G1Affine::generator() * (rprime * gammaprime_powers * output_b[j]))
                .to_affine();
            gammaprime_powers *= gammaprime;
        }

        let lhs_g1 = F + proof.0 .0 * eval_a + proof.1 .0 * (rprime * eval_b);
        let rhs_g1 = proof.0 .0 + (proof.1 .0 * rprime);

        let lhs_pairing = pairing(&lhs_g1.to_affine(), &G2Affine::generator());
        let rhs_pairing = pairing(&rhs_g1.to_affine(), &self.powers_x_g2[1]);

        if lhs_pairing == rhs_pairing {
            Ok(())
        } else {
            Err(())
        }
    }
}

impl<'a, 'b> Add<&'b Kzg10Commitment> for &'a Kzg10Commitment {
    type Output = Kzg10Commitment;

    fn add(self, rhs: &'b Kzg10Commitment) -> Self::Output {
        Kzg10Commitment((self.0 + G1Projective::from(&rhs.0)).to_affine())
    }
}

define_add_variants!(
    LHS = Kzg10Commitment,
    RHS = Kzg10Commitment,
    Output = Kzg10Commitment
);

impl<'a, 'b> Mul<&'b Scalar> for &'a Kzg10Commitment {
    type Output = Kzg10Commitment;

    fn mul(self, rhs: &'b Scalar) -> Self::Output {
        Kzg10Commitment((self.0 * rhs).to_affine())
    }
}

define_mul_variants!(
    LHS = Kzg10Commitment,
    RHS = Scalar,
    Output = Kzg10Commitment
);

impl<'a, 'b> Mul<&'b Kzg10Commitment> for &'a Scalar {
    type Output = Kzg10Commitment;

    fn mul(self, rhs: &'b Kzg10Commitment) -> Self::Output {
        rhs * self
    }
}

define_mul_variants!(
    LHS = Scalar,
    RHS = Kzg10Commitment,
    Output = Kzg10Commitment
);

#[cfg(test)]
mod tests {
    use super::*;

    const SIZE: usize = 10;
    #[test]
    fn test_setup() {
        let kzg10 = Kzg10::<SIZE>::setup();
        let toxic_waste = Scalar::random(&mut ChaCha20Rng::from_seed([0u8; 32]));

        assert_eq!(
            kzg10.powers_x_g2,
            [
                G2Affine::generator(),
                (G2Affine::generator() * toxic_waste).to_affine()
            ]
        );

        let mut powers_tw = G1Affine::generator();
        for val in kzg10.powers_x_g1 {
            assert_eq!(val, powers_tw);
            powers_tw = (powers_tw * toxic_waste).to_affine();
        }
    }

    #[test]
    fn test_kzg() {
        let kzg10 = Kzg10::<3>::setup();
        let mut transcript = Transcript::new(b"Testing KZG10");
        let mut transcript_verifier = Transcript::new(b"Testing KZG10");

        let polynomial1 = Polynomial(vec![Scalar::from(1), Scalar::from(5), Scalar::from(2)]);

        let polynomial2 = Polynomial(vec![Scalar::from(4), Scalar::from(5), Scalar::from(3)]);

        let eval_point1 = Scalar::from(3);
        let eval_point2 = Scalar::from(7);
        let result1 = polynomial1.eval(&eval_point1);
        let result2 = polynomial2.eval(&eval_point2);

        let commitment1 = kzg10.commit(&polynomial1);
        let commitment2 = kzg10.commit(&polynomial2);

        let proof = kzg10.batch_prove(
            &[polynomial1],
            &[polynomial2],
            &[commitment1.clone()],
            &[commitment2.clone()],
            &eval_point1,
            &eval_point2,
            &[result1],
            &[result2],
            &mut transcript,
        );

        assert!(kzg10
            .batch_verify(
                &proof,
                &[commitment1],
                &[commitment2],
                &eval_point1,
                &eval_point2,
                &[result1],
                &[result2],
                &mut transcript_verifier
            )
            .is_ok())
    }
}
