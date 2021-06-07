// This examples creates a circuit that proves knowledge of a message whose
// Pedersen hash equals a public value, given as public inputs. The value is
// constructed from two field Pasta elements and must be a valid point on the
// Vesta curve. The layout is as follow:
//
// +-----+------+----+---------+---------+
// | row |  msg |  r |  hash_x |  hash_y |
// +-----+------+----+---------+---------+
// | 0   | a    | r  |  x      | y       |
// +-----+------+----+---------+---------+
//
// then we want to prove that Point::from(hash_x,hash_y) == G^aH^r. For this

use halo2::circuit::{layouter::SingleChipLayouter, Cell, Chip, Layouter};
use halo2::dev::MockProver;
use halo2::pasta::Fp;
use halo2::plonk::{Advice, Assignment, Circuit, Column, ConstraintSystem, Error, Selector};
use halo2::poly::Rotation;

// We keep around the cell of an allocated value when we need to use it in
// subsequent rows so we can add it to the permutation argument (old row -> new
// row)
struct Alloc {
    cell: Cell,
    value: Fp,
}

#[derive(Debug, Clone)]
struct PedersenChip {
    config: PedersenConfig,
}

#[derive(Debug, Clone)]
struct PedersenConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    selector: Selector,
}

impl Chip<Fp> for PedersenChip {
    type Config = PedersenConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl PedersenChip {
    fn new(p: PedersenConfig) -> PedersenChip {
        PedersenChip { config: p }
    }

    fn configure(cs: &mut ConstraintSystem<Fp>) -> PedersenConfig {
        let a = cs.advice_column();
        let b = cs.advice_column();
        let c = cs.advice_column();
        let s = cs.selector();

        cs.create_gate("addition", |cs| {
            let aa = cs.query_advice(a, Rotation::cur());
            let bb = cs.query_advice(b, Rotation::cur());
            let cc = cs.query_advice(c, Rotation::cur());
            let mut select = cs.query_selector(s, Rotation::cur());
            select * (aa + bb - cc)
        });
        PedersenConfig {
            a,
            b,
            c,
            selector: s,
        }
    }

    fn allocate_inputs(
        &self,
        mut layouter: impl Layouter<Fp>,
        inputs: &Inputs,
    ) -> Result<(Alloc, Alloc, Alloc), Error> {
        layouter.assign_region(
            || "load inputs",
            |mut region| {
                // we enable the selector so the gate is enabled
                self.config.selector.enable(&mut region, 0);
                let acell =
                    region.assign_advice(|| "private a", self.config.a, 0, || Ok(inputs.a))?;
                let bcell =
                    region.assign_advice(|| "private b", self.config.b, 0, || Ok(inputs.b))?;
                let ccell =
                    region.assign_advice(|| "private c", self.config.c, 0, || Ok(inputs.c))?;
                let alloc = Alloc {
                    cell: acell,
                    value: inputs.a,
                };
                let blloc = Alloc {
                    cell: bcell,
                    value: inputs.b,
                };
                let clloc = Alloc {
                    cell: ccell,
                    value: inputs.c,
                };
                Ok((alloc, blloc, clloc))
            },
        )
    }
}

struct Inputs {
    pub a: Fp,
    pub b: Fp,
    pub c: Fp,
}

struct PedersenCircuit {
    inputs: Inputs,
}

impl Circuit<Fp> for PedersenCircuit {
    type Config = PedersenConfig;
    fn configure(cs: &mut ConstraintSystem<Fp>) -> Self::Config {
        PedersenChip::configure(cs)
    }

    fn synthesize(&self, cs: &mut impl Assignment<Fp>, config: Self::Config) -> Result<(), Error> {
        // create a new layouter that will organizes chips around
        let mut layouter = SingleChipLayouter::new(cs)?;
        let chip = PedersenChip::new(config);
        let res = chip.allocate_inputs(layouter.namespace(|| "addtion"), &self.inputs);
        match res {
            Ok((_, _, _)) => Ok(()),
            Err(e) => Err(e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_circuit_pedersen() {
        let circuit = PedersenCircuit {
            inputs: Inputs {
                a: Fp::from(10),
                b: Fp::from(20),
                c: Fp::from(30),
            },
        };
        let prover = MockProver::run(1, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_ok());
    }

    #[test]
    fn pasta_arithmetic() {
        let one = Fp::one();
        let zero = Fp::zero();
        assert!(one != zero);
    }
}
