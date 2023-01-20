use bls12_381::Scalar;
use std::ops::{Add, AddAssign, Div, Mul};

// Polynomial written as p(x) = a0 + x * a1 + .. + x^{MAX_DEGREE} * a_{MAX_DEGREE}, where we always pad with zeroes.
#[derive(Clone)]
pub struct Polynomial<const MAX_DEGREE: usize>(pub(crate) [Scalar; MAX_DEGREE]);

impl<const MAX_DEGREE: usize> Polynomial<MAX_DEGREE> {
    /// Evaluate a polynomial
    pub fn eval(&self, value: &Scalar) -> Scalar {
        let mut result = Scalar::zero();
        let mut power = Scalar::one();
        for coefficient in self.0 {
            result += power * coefficient;
            power *= value;
        }

        result
    }

    /// Create the zero polynomial
    pub fn zero() -> Self {
        Self([Scalar::zero(); MAX_DEGREE])
    }
}

impl<const MAX_DEGREE: usize> Add for Polynomial<MAX_DEGREE> {
    type Output = Polynomial<MAX_DEGREE>;

    fn add(self, rhs: Self) -> Self::Output {
        let mut out = [Scalar::zero(); MAX_DEGREE];
        let temp_vec = self
            .0
            .iter()
            .zip(rhs.0.iter())
            .map(|(left, right)| left + right)
            .collect::<Vec<Scalar>>();
        out.copy_from_slice(&temp_vec);
        Self(out)
    }
}

impl<const MAX_DEGREE: usize> AddAssign for Polynomial<MAX_DEGREE> {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.clone() + rhs;
    }
}

impl<'a, 'b, const MAX_DEGREE: usize> Mul<&'b Scalar> for &'a Polynomial<MAX_DEGREE> {
    type Output = Polynomial<MAX_DEGREE>;

    fn mul(self, rhs: &'b Scalar) -> Self::Output {
        let mut out = [Scalar::zero(); MAX_DEGREE];
        let temp_vec = self
            .0
            .iter()
            .map(|coeff| coeff * rhs)
            .collect::<Vec<Scalar>>();
        out.copy_from_slice(&temp_vec);
        Polynomial(out)
    }
}

// The following division algorithm is not generic. It's a simplification given that we
// know we are only going to use this with a monomial as a denominator.
// AND we know that the coefficient of the highest power is 1. todo: for now
impl<const MAX_DEGREE: usize> Div<Polynomial<2>> for Polynomial<MAX_DEGREE> {
    type Output = Polynomial<MAX_DEGREE>;

    fn div(self, rhs: Polynomial<2>) -> Self::Output {
        if rhs.0[1] != Scalar::one() {
            panic!("Unexpected denominator");
        }
        let mut result = Polynomial::<MAX_DEGREE>::zero();
        let mut carryover = Scalar::zero();
        for i in (1..MAX_DEGREE).rev() {
            result.0[i - 1] = self.0[i] - carryover;
            carryover = result.0[i - 1] * rhs.0[0];
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use crate::polynomial::Polynomial;
    use bls12_381::Scalar;

    #[test]
    fn eval() {
        let poly1 = Polynomial([
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
        let poly1 = Polynomial([
            Scalar::from(180),
            Scalar::from(3),
            Scalar::from(2),
            Scalar::from(7),
        ]);
        let poly2 = Polynomial([Scalar::from(3), Scalar::from(1)]);

        let poly3 = Polynomial([
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
        let poly1 = Polynomial([
            Scalar::from(5),
            Scalar::from(3),
            Scalar::from(2),
            Scalar::from(7),
        ]);
        let poly2 = Polynomial([
            Scalar::from(5),
            Scalar::from(3),
            Scalar::from(2),
            Scalar::from(7),
        ]);

        let poly3 = Polynomial([
            Scalar::from(10),
            Scalar::from(6),
            Scalar::from(4),
            Scalar::from(14),
        ]);

        assert_eq!(poly3.0, (poly1 + poly2).0);
    }
}
