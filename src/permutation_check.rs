// Given two polynomials, f, g of degree at most d, and a permutation
// \sigma : [n] -> [n], we say that g = \sigma(f) if g(g^i) = f(g^{\sigma(i)}),
// where `g` is a generator of order `n` of subgroup H \cup F.
//
// A permutation check allows a prover to convince a verifier that indeed
// g = \sigma(f).
//
// However, in Plonk we need to proof relations across several polynomials. Given
// k polynomials f_1, ..., f_k and a permutation \sigma : [kn] -> [kn]. We use
// the following notation, f_(1), ..., f(nk) to denote:
//
//          f_((j-1) * n + i) := f_j(g^i).
//
// Then, for g_1, ..., g_k, we say that (g_1, ..., g_k) = \sigma(f_1, ..., f_k)
// if g(l) = f(\sigma(l)).

use crate::polynomial::{Polynomial, PolynomialEvaluationPoints};
use crate::transcript::Transcript;
use blstrs::Scalar;
use ff::{Field, PrimeField};
use std::collections::{HashMap, HashSet};

// There is k of them, of degree n-1
pub struct PermutationArgument {
    polynomials: Vec<Polynomial>,
    permuted_polys: Vec<Polynomial>,
    degree: usize,
    nth_root_unity: Scalar,
}

pub struct Permutation(HashMap<usize, usize>);

pub type PermutationProof = Polynomial;

impl Permutation {
    pub fn new(permutation: Vec<Vec<usize>>) -> Self {
        let mut map = HashMap::new();
        // We check that the permutation has no repeated elements
        let mut uniq = HashSet::new();
        assert!(
            permutation.iter().flatten().all(move |x| uniq.insert(x)),
            "Invalid permutation"
        );

        for perms in permutation {
            for (position, &value) in perms.iter().enumerate() {
                if position == (perms.len() - 1) {
                    map.insert(value, perms[0]);
                    continue;
                }
                map.insert(value, perms[position + 1]);
            }
        }

        Self(map)
    }

    pub fn permute(&self, val: &usize) -> usize {
        *self.0.get(val).expect("Value out of bounds of permutation")
    }
}

impl PermutationArgument {
    pub fn setup(permutation: Permutation, k: usize, n: usize) -> Self {
        let mut polynomials = Vec::with_capacity(k);
        let mut permuted_polys = Vec::with_capacity(k);
        for j in 1..=k {
            let mut eval_points = Vec::with_capacity(n);
            let mut eval_points_perm = Vec::with_capacity(n);
            for i in 1..=n {
                let exponent = [i as u64, 0, 0, 0];
                eval_points.push((
                    Scalar::root_of_unity().pow_vartime(&exponent),
                    Scalar::from(((j - 1) * n + i) as u64),
                ));
                eval_points_perm.push((
                    Scalar::root_of_unity().pow_vartime(&exponent),
                    Scalar::from(permutation.permute(&((j - 1) * n + i)) as u64),
                ));
            }
            polynomials.push(PolynomialEvaluationPoints(eval_points).interpolate());
            permuted_polys.push(PolynomialEvaluationPoints(eval_points_perm).interpolate())
        }

        Self {
            polynomials,
            permuted_polys,
            degree: n,
            nth_root_unity: Scalar::root_of_unity().pow_vartime(&[(1u64 << 32) / n as u64, 0, 0, 0]),
        }
    }

    pub fn prove(
        &self,
        f_polys: &[Polynomial],
        g_polys: &[Polynomial],
        transcript: &mut Transcript,
    ) -> PermutationProof {
        assert_eq!(
            f_polys.len(),
            g_polys.len(),
            "Polynomials need to be equal length"
        );

        let mut z_eval_points = Vec::with_capacity(self.degree);

        for poly in f_polys {
            for coeff in &poly.0 {
                transcript.append_scalar(b"freference", &coeff); // label should change at each iteration for security, but for sake of simplicity, we'll leave it as is
            }
        }

        for poly in g_polys {
            for coeff in &poly.0 {
                transcript.append_scalar(b"greference", &coeff); // label should change at each iteration for security, but for sake of simplicity, we'll leave it as is
            }
        }

        let beta = transcript.challenge_scalar(b"beta");
        let gamma = transcript.challenge_scalar(b"gamma");

        let mut fprimes = Polynomial::zero(self.degree);
        let mut gprimes = Polynomial::zero(self.degree);

        // TODO: In the paper there is a simple optimisation for this. If this gets too expensive, then
        // go back to the paper, and improve.
        for (index, poly) in f_polys.iter().enumerate() {
            fprimes *= poly + &(&self.polynomials[index] * &beta + &gamma);
        }

        for (index, poly) in g_polys.iter().enumerate() {
            gprimes *= poly + (&self.permuted_polys[index] * &beta + &gamma);
        }

        z_eval_points.push((Scalar::root_of_unity(), Scalar::one()));
        for index in 2..=self.degree {
            let mut result = Scalar::one();
            for j in 1..=index {
                let exponent = [j as u64, 0, 0, 0];
                result *= fprimes.eval(&Scalar::root_of_unity().pow_vartime(&exponent))
                    * gprimes
                        .eval(&Scalar::root_of_unity().pow_vartime(&exponent))
                        .invert()
                        .unwrap();
            }
            let exponent = [index as u64, 0, 0, 0];
            z_eval_points.push((Scalar::root_of_unity().pow_vartime(&exponent), result));
        }

        PolynomialEvaluationPoints(z_eval_points).interpolate()
    }

    pub fn verify(&self, _proof: PermutationProof) -> Result<(), ()> {
        // TODO: WOW, here we have to verify for each element of the subgroup? This seems a lot. I think
        // here we have the probabilistic part.
        Ok(())
    }
}

// Temporarily we'll set the generator `g` of the subgroup as 11
// const GENERATOR: Scalar = Scalar::from(11);
