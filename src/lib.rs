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

use group::prime::PrimeCurveAffine;
use group::{Group, ScalarMul};
use halo2::circuit::{layouter::RegionLayouter, Cell, Chip, Layouter, SimpleFloorPlanner};
use halo2::dev::MockProver;
use halo2::pasta::Fp;
use halo2::plonk::{Advice, Assignment, Circuit, Column, ConstraintSystem, Error, Selector};
use halo2::poly::Rotation;
use orchard::circuit::gadget::ecc::chip::{EccChip, EccConfig};
use orchard::circuit::gadget::ecc::EccInstructions; // required to use mul in circuit
use orchard::circuit::gadget::ecc::{Point, ScalarFixed, ScalarVar};
use orchard::circuit::gadget::utilities::lookup_range_check::LookupRangeCheckConfig;
use orchard::circuit::gadget::utilities::UtilitiesInstructions;
use pasta_curves::{arithmetic::CurveAffine, pallas};

use std::marker::PhantomData;
use std::ops::MulAssign;

use ff::PrimeFieldBits;
//mod verkle;

#[derive(Debug, Clone)]
struct PedersenChip<C: CurveAffine> {
    config: PedersenConfig,
    ecc: EccChip,
    phantom: PhantomData<C>,
}

#[derive(Debug, Clone)]
struct PedersenConfig {
    col1: Column<Advice>,
    col2: Column<Advice>,
    col3: Column<Advice>,
    ecc_config: EccConfig,
}

impl<C> Chip<C::Base> for PedersenChip<C>
where
    C: CurveAffine,
{
    type Config = PedersenConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<C> PedersenChip<C>
where
    C: CurveAffine,
    C::Base: PrimeFieldBits,
{
    fn new(p: PedersenConfig) -> PedersenChip<C> {
        PedersenChip {
            ecc: EccChip::construct(p.ecc_config.clone()),
            config: p,
            phantom: PhantomData<C>,
        }
    }

    fn configure(meta: &mut ConstraintSystem<C::Base>) -> PedersenConfig {
        let advices = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];
        let lookup_table = meta.lookup_table_column();
        let lagrange_coeffs = [
            meta.fixed_column(),
            meta.fixed_column(),
            meta.fixed_column(),
            meta.fixed_column(),
            meta.fixed_column(),
            meta.fixed_column(),
            meta.fixed_column(),
            meta.fixed_column(),
        ];
        // Shared fixed column for loading constants
        let constants = meta.fixed_column();
        meta.enable_constant(constants);

        let range_check = LookupRangeCheckConfig::configure(meta, advices[9], lookup_table);
        let ecc_config = EccChip::configure(meta, advices, lagrange_coeffs, range_check);
        let col1 = meta.advice_column();
        meta.enable_equality(col1.into());
        let col2 = meta.advice_column();
        meta.enable_equality(col2.into());
        let col3 = meta.advice_column();
        meta.enable_equality(col3.into());

        PedersenConfig {
            col1,
            col2,
            col3,
            ecc_config,
        }
    }
}

// pallas::Base = Fp
// pallas::Scalar = Fq
// vesta::Base = Fq
// vesta::Scalar = Fp
// we construct circuit with elements of the circuit be pallas::Base = Fp so the
// curve points we're gonna use are on pallas (Fp, Fp) -> |E(Fp)| = Fq
// HOWEVER: given halo2/orchard doesn't support variable base multiplication,
// and they use the right field size they only currently allow for a Fp * G
// multiplication
struct Inputs<C: CurveAffine> {
    pub e: C::Base,
    pub f: C::Base,
    pub g: C::Base,
}

struct PedersenCircuit<C: CurveAffine> {
    inputs: Inputs<C>,
}

// We have the circuit over C::Base that means the arithmetic circuit has
// elements in C::Base. That means proof will contain points in curve
// C2  with C2::Scalar == C::Base. In our case C = Pallas therefore C2 = Vesta
// The input to the circuit are C::Base elements so to perform group
// arithmetic in the circuit, we have to use points in C2.
impl<C> Circuit<C::Base> for PedersenCircuit<C>
where
    C: CurveAffine,
    C::Base: PrimeFieldBits,
{
    type Config = PedersenConfig;
    type FloorPlanner = SimpleFloorPlanner;
    //type Config = EccConfig;
    fn configure(cs: &mut ConstraintSystem<C::Base>) -> Self::Config {
        PedersenChip::configure(cs)
    }
    fn without_witnesses(&self) -> Self {
        Self::default()
    }
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Base>,
    ) -> Result<(), Error> {
        let chip = PedersenChip::new(config);
        // allocate inputs for the point addition
        // [e] + [f] = [g]
        println!(" LETS SEE!!");
        /*let e = ScalarFix::new(*/
        //chip.ecc.clone(),
        //&mut layouter.namespace(|| "scalar witness"),
        //Some(self.inputs.e),
        /*)?;*/
        let e = chip.ecc.load_private(
            &mut layouter.namespace(|| "witness"),
            chip.config.col1,
            Some(self.inputs.e),
        )?;
        /*let base = Point::new(*/
        //chip.ecc.clone(),
        //&mut layouter.namespace(|| "generator"),
        //Some(pallas::generator()),
        /*)?;*/
        let base = chip.ecc.witness_point_non_id(
            &mut layouter.namespace(|| "generator"),
            Some(pallas::Affine::generator()),
        )?;
        let (ep, _) = chip.ecc.mul(&mut layouter.namespace(|| "[e]"), &e, &base)?;
        let f = chip.ecc.load_private(
            //let scalar_var = ecc.witness_scalar_fixed(
            &mut layouter.namespace(|| "scalar witness"),
            chip.config.col2,
            Some(self.inputs.f),
        )?;
        let g = chip.ecc.load_private(
            //let scalar_var = ecc.witness_scalar_fixed(
            &mut layouter.namespace(|| "scalar witness"),
            chip.config.col3,
            Some(self.inputs.g),
        )?;
        println!(" THIS WORKS!!");
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2::pasta::pallas::Affine;
    #[test]
    fn test_circuit_pedersen() {
        let mut circuit: PedersenCircuit = PedersenCircuit {
            inputs: Inputs {
                e: pallas::Base::from(10),
                f: pallas::Base::from(20),
                g: pallas::Base::from(30),
            },
        };
        let prover = MockProver::run(12, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_ok());

        /*circuit.inputs.e = <Affine as CurveAffine>::ScalarExt::from(59);*/
        //let prover = MockProver::run(12, &circuit, vec![]).unwrap();
        /*assert!(prover.verify().is_err());*/
    }

    #[test]
    fn pasta_arithmetic() {
        let one = Fp::one();
        let zero = Fp::zero();
        assert!(one != zero);
    }
}
