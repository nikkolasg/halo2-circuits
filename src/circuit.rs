use group::{Curve, Group};
use halo2::arithmetic::FieldExt;
use halo2::circuit::{Chip, Layouter, SimpleFloorPlanner};
use halo2::dev::MockProver;
use halo2::pasta::Fp;
use halo2::plonk::{Advice, Circuit, Column, ConstraintSystem, Error};
use orchard::circuit::gadget::ecc::chip::{EccChip, EccConfig};
use orchard::circuit::gadget::ecc::NonIdentityPoint;
use orchard::circuit::gadget::utilities::lookup_range_check::LookupRangeCheckConfig;
use orchard::circuit::gadget::utilities::UtilitiesInstructions;
//use pasta_curves::{arithmetic::CurveAffine, pallas};
use pasta_curves::pallas;

#[derive(Debug, Clone)]
struct PedersenChip {
    config: PedersenConfig,
    ecc: EccChip,
}

/*impl UtilitiesInstructions<pallas::Base> for PedersenChip {*/
//type Var = CellValue<pallas::Base>;
//}

#[derive(Debug, Clone)]
struct PedersenConfig {
    col1: Column<Advice>,
    col2: Column<Advice>,
    col3: Column<Advice>,
    ecc_config: EccConfig,
}

impl Chip<pallas::Base> for PedersenChip {
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
        PedersenChip {
            ecc: EccChip::construct(p.ecc_config.clone()),
            config: p,
        }
    }

    fn configure(meta: &mut ConstraintSystem<pallas::Base>) -> PedersenConfig {
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
#[derive(Default)]
struct PedersenCircuit {
    pub e: Option<pallas::Base>,
    pub f: Option<pallas::Base>,
    pub g: Option<pallas::Base>,
}
// We have the circuit over C::Base that means the arithmetic circuit has
// elements in C::Base. That means proof will contain points in curve
// C2  with C2::Scalar == C::Base. In our case C = Pallas therefore C2 = Vesta
// The input to the circuit are C::Base elements so to perform group
// arithmetic in the circuit, we have to use points in C2.
impl Circuit<pallas::Base> for PedersenCircuit {
    type Config = PedersenConfig;
    type FloorPlanner = SimpleFloorPlanner;
    //type Config = EccConfig;
    fn configure(cs: &mut ConstraintSystem<pallas::Base>) -> Self::Config {
        PedersenChip::configure(cs)
    }
    fn without_witnesses(&self) -> Self {
        Self::default()
    }
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<pallas::Base>,
    ) -> Result<(), Error> {
        let chip = PedersenChip::new(config);
        // allocate inputs for the point addition
        // [e] + [f] = [g]
        //let _ = chip.ecc.load_private(
        //layouter.namespace(|| "witness2"),
        //chip.config.col2,
        //Some(self.inputs.f),
        //)?;
        //let _ = chip.ecc.load_private(
        //layouter.namespace(|| "witness3"),
        //chip.config.col3,
        //Some(self.inputs.g),
        //)?;
        //
        //
        let scalar_val = pallas::Base::rand();
        let e = chip.ecc.load_private(
            layouter.namespace(|| "witness1"),
            chip.ecc.config().advices[0],
            Some(scalar_val),
        )?;
        let p_val = pallas::Point::random(rand::rngs::OsRng).to_affine();
        let p_cell =
            NonIdentityPoint::new(chip.ecc.clone(), layouter.namespace(|| "b1"), Some(p_val))?;
        let (_, _) = p_cell.mul(layouter.namespace(|| "[e]B"), &e)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_circuit_pedersen() {
        let circuit: PedersenCircuit = PedersenCircuit {
            e: Some(pallas::Base::from(10)),
            f: Some(pallas::Base::from(20)),
            g: Some(pallas::Base::from(30)),
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
