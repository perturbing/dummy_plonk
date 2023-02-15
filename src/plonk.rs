// We begin implementing the plonk circuit. For sake of simplicity
// we only create two gadgets. ADD and MULT. Maybe in the future
// we will experiment with custom gates.
//
// Recall that plonk gates are defined by:
//
// q_L * a + q_R * b + q_O * c + q_M * ab + q_C = 0
//
// where a, b, c are the left, right and output wires of the gate.
//
// So, if we want to add as a constraint 5 * 3 = 15, then we would set
//
// q_L = q_R = q_C = 0, q_O = -1, q_M = 1
//
// To view this clearly, we represent each plonk gate by a [Scalar; 5],
// meaning that a circuit will be created by Vec<[Scalar; 5]>, with its
// length being the number of constraints we include in the circuit, e.g. :
//
//           | q_L |    |  0,  1, ... ,  0|
//           | q_R |    |  0,  1, ... ,  0|
// Circuit = | q_O | =  | -1, -1, ... , -1|
//           | q_M |    |  1,  0, ... ,  1|
//           | q_C |    |  0,  0, ... ,  0|
//
// The trace is the left, right and output values of each constraint.
//
// We also need to declare the connections between the wires. For that, we require
// the circuit designer to specify which two wires are connected. For sake
// of simplicity, we are only exposing an addition and a multiplication gate. Each
// one of these gates increases the total number of wires by 3, so it should be easy
// to keep the count in our examples.
#![allow(non_snake_case)]
use crate::kzg10::Kzg10;
use crate::polynomial::Polynomial;
use blstrs::Scalar;
use ff::{Field, PrimeField};
use std::collections::HashMap;
use std::ops::Neg;

pub(crate) fn K1() -> Scalar {
    Scalar::from(7_u64)
}
pub(crate) fn K2() -> Scalar {
    Scalar::from(13_u64)
}

pub struct ComputationTrace {
    pub(crate) a: Vec<Scalar>,
    pub(crate) b: Vec<Scalar>,
    pub(crate) c: Vec<Scalar>,
}

impl ComputationTrace {
    pub(crate) fn pad_next_power_two(&self) -> Self {
        let new_size = self.a.len().next_power_of_two();
        let mut result = ComputationTrace {
            a: vec![Scalar::zero(); new_size],
            b: vec![Scalar::zero(); new_size],
            c: vec![Scalar::zero(); new_size],
        };

        result.a[..self.a.len()].copy_from_slice(&self.a);
        result.b[..self.b.len()].copy_from_slice(&self.b);
        result.c[..self.c.len()].copy_from_slice(&self.c);

        result
    }
}

#[derive(Clone, Default)]
pub struct Constraints {
    pub qm: Vec<Scalar>,
    pub ql: Vec<Scalar>,
    pub qr: Vec<Scalar>,
    pub qo: Vec<Scalar>,
    pub qc: Vec<Scalar>,
}

#[derive(Clone)]
pub struct PlonkCircuit {
    pub extended_h_subgroup: Vec<Scalar>,
    pub constraints: Constraints,
    pub permutations: HashMap<usize, usize>,
    pub nr_wires: usize,
    pub nr_constraints: usize,
}

pub struct PlonkConstraintSystem(ComputationTrace, PlonkCircuit);

pub struct PreprocessedInput {
    pub kzg_set: Kzg10<128>, // We could make this generic, but it's only going to complicate the code.
    pub blinder_polynomial: Polynomial,
    pub constraints: PlonkCircuit,
    pub sigma_star: HashMap<usize, Scalar>,
    pub qm_x: Polynomial,
    pub ql_x: Polynomial,
    pub qr_x: Polynomial,
    pub qo_x: Polynomial,
    pub qc_x: Polynomial,
    pub qs1_x: Polynomial,
    pub qs2_x: Polynomial,
    pub qs3_x: Polynomial,
}

impl PlonkCircuit {
    pub fn init() -> Self {
        Self {
            constraints: Default::default(),
            permutations: Default::default(),
            nr_wires: 0,
            nr_constraints: 0,
            extended_h_subgroup: Default::default(),
        }
    }
    pub fn add_gate(&mut self) {
        self.constraints.ql.push(Scalar::one());
        self.constraints.qr.push(Scalar::one());
        self.constraints.qo.push(Scalar::one().neg());
        self.constraints.qm.push(Scalar::zero());
        self.constraints.qc.push(Scalar::zero());

        // we extend the permutation with the identity permutation
        self.permutations.insert(self.nr_wires, self.nr_wires);
        self.permutations
            .insert(self.nr_wires + 1, self.nr_wires + 1);
        self.permutations
            .insert(self.nr_wires + 2, self.nr_wires + 2);

        self.nr_wires += 3;
        self.nr_constraints += 1;
    }

    pub fn mult_gate(&mut self) {
        self.constraints.qm.push(Scalar::one());
        self.constraints.qo.push(Scalar::one().neg());
        self.constraints.ql.push(Scalar::zero());
        self.constraints.qr.push(Scalar::zero());
        self.constraints.qc.push(Scalar::zero());

        // we extend the permutation with the identity permutation
        self.permutations.insert(self.nr_wires, self.nr_wires);
        self.permutations
            .insert(self.nr_wires + 1, self.nr_wires + 1);
        self.permutations
            .insert(self.nr_wires + 2, self.nr_wires + 2);

        self.nr_wires += 3;
        self.nr_constraints += 1;
    }

    pub fn prepare_pi(&mut self) {
        self.constraints.ql.push(Scalar::one());
        self.constraints.qr.push(Scalar::zero());
        self.constraints.qo.push(Scalar::zero());
        self.constraints.qm.push(Scalar::zero());
        self.constraints.qc.push(Scalar::zero());

        // we extend the permutation with the identity permutation
        self.permutations.insert(self.nr_wires, self.nr_wires);
        self.permutations
            .insert(self.nr_wires + 1, self.nr_wires + 1);
        self.permutations
            .insert(self.nr_wires + 2, self.nr_wires + 2);

        self.nr_wires += 3;
        self.nr_constraints += 1;
    }

    // Pad to the next power of two
    pub fn pad_next_power_of_two(&mut self) {
        // we first pad the number of constraints to the next power of two. we do so by adding zero constraints
        while (self.nr_constraints & (self.nr_constraints - 1)) != 0 {
            self.add_gate();
        }
    }

    // This should always be called after creating the gates.
    pub fn connect_wires(&mut self, in_wire: &usize, out_wire: &usize) {
        assert!(*in_wire < self.nr_wires && *out_wire < self.nr_wires, "The circuit does not have enough wires for these two. Max {0}, got {in_wire} and {out_wire}", self.nr_wires);
        let in_rel = self.permutations.get(in_wire).unwrap().clone(); // we know each key is populated
        let out_rel = self.permutations.get(out_wire).unwrap().clone(); // we know each key is populated
        self.permutations.insert(*in_wire, out_rel);
        self.permutations.insert(*out_wire, in_rel);
    }

    pub fn lagrange_basis(&self, index: usize) -> Polynomial {
        let mut lb = Polynomial(vec![Scalar::from(1)]);
        for j in 0..self.nr_constraints {
            if index == j {
                continue;
            }

            lb *= &Polynomial(vec![self.extended_h_subgroup[j].neg(), Scalar::one()])
                * (self.extended_h_subgroup[index] - self.extended_h_subgroup[j])
                    .invert()
                    .unwrap();
        }
        lb
    }

    pub fn compute_sigma_star(&self) -> HashMap<usize, Scalar> {
        self.permutations
            .iter()
            .map(|(index, value)| (*index, self.extended_h_subgroup[*value]))
            .collect::<HashMap<usize, Scalar>>()
    }

    pub fn setup(&mut self) -> PreprocessedInput {
        // For simplicity, we begin computing our extended subgroup H'. We need an nth root of unity with
        // n being the number of constraints. We compute this root of unity out of the 2^32nd
        // root of unity, g, which is provided as a constant in the underlying library. We do so
        // by calculating omega = g^{2^32/ n}.
        let omega = Scalar::root_of_unity().pow_vartime([
            (1u64 << 32) / self.nr_constraints as u64,
            0,
            0,
            0,
        ]);

        assert_eq!(
            omega.pow_vartime([self.nr_constraints as u64, 0, 0, 0]),
            Scalar::one()
        );

        self.extended_h_subgroup = vec![Scalar::zero(); self.nr_constraints * 3];
        self.extended_h_subgroup[0] = omega;
        self.extended_h_subgroup[self.nr_constraints] = K1() * omega;
        self.extended_h_subgroup[self.nr_constraints * 2] = K2() * omega;

        for index in 1..self.nr_constraints {
            self.extended_h_subgroup[index] = self.extended_h_subgroup[index - 1] * omega;
            self.extended_h_subgroup[index + self.nr_constraints] =
                self.extended_h_subgroup[index] * K1();
            self.extended_h_subgroup[index + self.nr_constraints * 2] =
                self.extended_h_subgroup[index] * K2();
        }

        // Next, we define the \sigma*
        let sigma_star = self.compute_sigma_star();

        // Now we create the permutation polynomials qs1, qs2 and qs3, and the
        // selector polynomials ql_x, qr_x, qc_x, qo_x and qm_x.
        let mut qs1_x = Polynomial::zero(self.nr_constraints);
        let mut qs2_x = Polynomial::zero(self.nr_constraints);
        let mut qs3_x = Polynomial::zero(self.nr_constraints);

        let mut ql_x = Polynomial::zero(self.nr_constraints);
        let mut qr_x = Polynomial::zero(self.nr_constraints);
        let mut qc_x = Polynomial::zero(self.nr_constraints);
        let mut qo_x = Polynomial::zero(self.nr_constraints);
        let mut qm_x = Polynomial::zero(self.nr_constraints);

        for i in 0..self.nr_constraints {
            let lp = self.lagrange_basis(i);
            qs1_x += &lp * sigma_star.get(&i).unwrap();
            qs2_x += &lp * sigma_star.get(&(self.nr_constraints + i)).unwrap();
            qs3_x += &lp * sigma_star.get(&(self.nr_constraints * 2 + i)).unwrap();

            ql_x += &lp * self.constraints.ql[i];
            qr_x += &lp * self.constraints.qr[i];
            qc_x += &lp * self.constraints.qc[i];
            qo_x += &lp * self.constraints.qo[i];
            qm_x += &lp * self.constraints.qm[i];
        }

        let mut blinder_vec = vec![Scalar::zero(); self.nr_constraints + 1];
        blinder_vec[0] = Scalar::one().neg();
        blinder_vec[self.nr_constraints] = Scalar::one();
        let blinder_polynomial = Polynomial(blinder_vec);
        assert!(self.extended_h_subgroup[..self.nr_constraints]
            .iter()
            .all(|val| blinder_polynomial.eval(val) == Scalar::zero()));

        PreprocessedInput {
            kzg_set: Kzg10::setup(),
            blinder_polynomial,
            sigma_star,
            qm_x,
            ql_x,
            qr_x,
            qo_x,
            qc_x,
            qs1_x,
            qs2_x,
            qs3_x,
            constraints: self.clone(),
        }
    }
}
