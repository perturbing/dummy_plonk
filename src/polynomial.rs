use crate::*;
use bls12_381::Scalar;
use std::cmp::min;
use std::collections::HashMap;
use std::ops::{Add, AddAssign, Div, Mul, MulAssign};
#[macro_use]
use crate::macros::*;

// Polynomial written as p(x) = a0 + x * a1 + .. + x^{MAX_DEGREE} * a_{MAX_DEGREE}, where we always pad with zeroes.
#[derive(Clone)]
pub struct Polynomial(pub(crate) Vec<Scalar>);

impl Polynomial {
    /// Evaluate a polynomial
    pub fn eval(&self, value: &Scalar) -> Scalar {
        let mut result = Scalar::zero();
        let mut power = Scalar::one();
        for coefficient in self.0.iter() {
            result += power * coefficient;
            power *= value;
        }

        result
    }

    /// Create the zero polynomial
    pub fn zero(degree: usize) -> Self {
        Self(vec![Scalar::zero(); degree])
    }
}

impl<'a, 'b> Add<&'b Polynomial> for &'a Polynomial {
    type Output = Polynomial;

    fn add(self, rhs: &'b Polynomial) -> Self::Output {
        let min_degree = min(self.0.len(), rhs.0.len());
        let mut result = if self.0.len() > rhs.0.len() {
            self.clone()
        } else {
            rhs.clone()
        };
        for index in 0..min_degree {
            result.0[index] = self.0[index] + rhs.0[index]
        }

        result
    }
}

define_add_variants!(LHS = Polynomial, RHS = Polynomial, Output = Polynomial);

impl<'b> AddAssign<&'b Polynomial> for Polynomial {
    fn add_assign(&mut self, rhs: &'b Self) {
        *self = self.clone() + rhs;
    }
}

define_add_assign_variants!(LHS = Polynomial, RHS = Polynomial);

impl<'a, 'b> Add<&'b Scalar> for &'a Polynomial {
    type Output = Polynomial;

    fn add(self, rhs: &'b Scalar) -> Self::Output {
        let mut vec = self.0.clone();
        vec[0] += rhs;
        Polynomial(vec)
    }
}

define_add_variants!(LHS = Polynomial, RHS = Scalar, Output = Polynomial);

impl<'a, 'b> Mul<&'b Scalar> for &'a Polynomial {
    type Output = Polynomial;

    fn mul(self, rhs: &'b Scalar) -> Self::Output {
        Polynomial(
            self.0
                .iter()
                .map(|coeff| coeff * rhs)
                .collect::<Vec<Scalar>>(),
        )
    }
}

define_mul_variants!(LHS = Polynomial, RHS = Scalar, Output = Polynomial);

impl<'a, 'b> Mul<&'b Polynomial> for &'a Polynomial {
    type Output = Polynomial;

    fn mul(self, rhs: &'b Polynomial) -> Self::Output {
        let mut out = vec![Scalar::zero(); self.0.len() + rhs.0.len() - 1];
        for (idx_a, coeff_a) in self.0.iter().enumerate() {
            for (idx_b, coeff_b) in rhs.0.iter().enumerate() {
                out[idx_a + idx_b] += coeff_a * coeff_b;
            }
        }

        Polynomial(out)
    }
}

define_mul_variants!(LHS = Polynomial, RHS = Polynomial, Output = Polynomial);

impl<'b> MulAssign<&'b Polynomial> for Polynomial {
    fn mul_assign(&mut self, rhs: &'b Self) {
        *self = &self.clone() * rhs;
    }
}

define_mul_assign_variants!(LHS = Polynomial, RHS = Polynomial);

// The following division algorithm is not generic. It's a simplification given that we
// know we are only going to use this with a monomial as a denominator.
// AND we know that the coefficient of the highest power is 1. todo: for now
impl Div<Polynomial> for Polynomial {
    type Output = Polynomial;

    fn div(self, rhs: Polynomial) -> Self::Output {
        if rhs.0[1] != Scalar::one() {
            panic!("Unexpected denominator");
        }

        if rhs.0.len() != 2 {
            panic!("Unexpected denominator");
        }

        let mut result = Polynomial::zero(self.0.len());
        let mut carryover = Scalar::zero();
        for i in (1..self.0.len()).rev() {
            result.0[i - 1] = self.0[i] - carryover;
            carryover = result.0[i - 1] * rhs.0[0];
        }

        result
    }
}

// Polynomial represented as Evaluation points (I don't think we'll implement
// the Fast Fourier Transform, as the goal here is not efficiency, but rather
// simplicity).
// We are assuming multiplicative subgroup of order `n`, meaning that each power
// of the generator `g` will be different.
pub struct PolynomialEvaluationPoints(pub(crate) Vec<(Scalar, Scalar)>);

impl PolynomialEvaluationPoints {
    pub fn interpolate(&self) -> Polynomial {
        let mut polynomial = Polynomial::zero(self.0.len());
        for i in 0..self.0.len() {
            let mut lb = Polynomial(vec![Scalar::from(1)]);
            for j in 0..self.0.len() {
                if i == j {
                    continue;
                }
                lb *= &Polynomial(vec![self.0[j].0.neg(), Scalar::one()])
                    * &(self.0[i].0 - self.0[j].0).invert().unwrap();
            }

            polynomial += &lb * &self.0[i].1;
        }

        polynomial
    }
}

#[cfg(test)]
mod tests {
    use crate::polynomial::{Polynomial, PolynomialEvaluationPoints};
    use bls12_381::Scalar;

    #[test]
    fn eval() {
        let poly1 = Polynomial(vec![
            Scalar::from(5),
            Scalar::from(3),
            Scalar::from(2),
            Scalar::from(7),
        ]);

        let eval_point = Scalar::from(3);
        let result = Scalar::from(221);

        assert_eq!(result, poly1.eval(&eval_point));
    }

    #[test]
    fn test_division() {
        let poly1 = Polynomial(vec![
            Scalar::from(180),
            Scalar::from(3),
            Scalar::from(2),
            Scalar::from(7),
        ]);
        let poly2 = Polynomial(vec![Scalar::from(3), Scalar::from(1)]);

        let poly3 = Polynomial(vec![
            Scalar::from(60),
            Scalar::from(19).neg(),
            Scalar::from(7),
            Scalar::zero(),
        ]);
        let div = poly1 / poly2;

        assert_eq!(poly3.0, div.0);
    }

    #[test]
    fn test_addition() {
        let poly1 = Polynomial(vec![
            Scalar::from(5),
            Scalar::from(3),
            Scalar::from(2),
            Scalar::from(7),
        ]);
        let poly2 = Polynomial(vec![
            Scalar::from(5),
            Scalar::from(3),
            Scalar::from(2),
            Scalar::from(7),
        ]);

        let poly3 = Polynomial(vec![
            Scalar::from(10),
            Scalar::from(6),
            Scalar::from(4),
            Scalar::from(14),
        ]);

        assert_eq!(poly3.0, (poly1 + poly2).0);
    }

    #[test]
    fn test_mult() {
        let poly1 = Polynomial(vec![
            Scalar::from(180),
            Scalar::from(3),
            Scalar::from(2),
            Scalar::from(7),
        ]);
        let poly2 = Polynomial(vec![Scalar::from(3), Scalar::from(1)]);

        let poly3 = Polynomial(vec![
            Scalar::from(60),
            Scalar::from(19).neg(),
            Scalar::from(7),
        ]);

        assert_eq!(poly1.0, (&poly2 * &poly3).0);
    }

    #[test]
    fn test_interpolation() {
        let poly1 = Polynomial(vec![
            Scalar::from(180),
            Scalar::from(3),
            Scalar::from(2),
            Scalar::from(7),
            Scalar::from(11145),
            Scalar::from(13461346).neg(),
            Scalar::from(1).neg(),
        ]);

        let eval_points: Vec<(Scalar, Scalar)> = (0..poly1.0.len())
            .map(|i| (Scalar::from(i as u64), poly1.eval(&Scalar::from(i as u64))))
            .collect();
        let eval_poly = PolynomialEvaluationPoints(eval_points);

        assert_eq!(poly1.0, eval_poly.interpolate().0);
    }
}
