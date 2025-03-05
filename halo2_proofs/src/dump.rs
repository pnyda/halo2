#![allow(missing_docs)]

use std::ops::Range;

use ff::Field;

use crate::circuit::Value;
use crate::plonk::Expression;
use crate::plonk::{
    Advice, Any, Assigned, Assignment, Circuit, Column, ConstraintSystem, Error, Fixed, Instance,
    Selector,
};

#[derive(Debug, PartialEq)]
pub struct CopyConstraint {
    pub from_column_type: Any,
    pub from_column_index: usize,
    pub from_row_index: usize,
    pub to_column_type: Any,
    pub to_column_index: usize,
    pub to_row_index: usize,
}

/// Visit a circuit and keep track of cell assignment.
#[derive(Debug)]
pub struct AssignmentDumper<F: Field> {
    pub k: u32,

    pub copy_constraints: Vec<CopyConstraint>,
    // instance[column_index][row_index] == cell_value
    pub instance: Vec<Vec<Value<F>>>,
    // fixed[column_index][row_index] == cell_value
    pub fixed: Vec<Vec<Option<F>>>,
    // selectors[column_index][row_index] == cell_value
    pub selectors: Vec<Vec<bool>>,
    // advice[column_index][row_index] == cell_value
    pub advice: Vec<Vec<Option<F>>>,
    // A range of available rows for assignment and copies.
    pub usable_rows: Range<usize>,
}

impl<F: Field> AssignmentDumper<F> {
    pub fn new(k: u32, meta: &ConstraintSystem<F>) -> Self {
        let usable_rows = (1 << k) - meta.blinding_factors() - 1;

        AssignmentDumper {
            k,
            instance: vec![vec![Value::unknown(); usable_rows]; meta.num_instance_columns],
            fixed: vec![vec![None; usable_rows]; meta.num_fixed_columns],
            advice: vec![vec![None; usable_rows]; meta.num_advice_columns],
            selectors: vec![vec![false; usable_rows]; meta.num_selectors],
            copy_constraints: Vec::new(),
            usable_rows: 0..usable_rows,
        }
    }
}

// Based on keygen.rs.
impl<F: Field> Assignment<F> for AssignmentDumper<F> {
    fn enter_region<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about regions in this context.
    }

    fn exit_region(&mut self) {
        // Do nothing; we don't care about regions in this context.
    }

    fn enable_selector<A, AR>(&mut self, _: A, selector: &Selector, row: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        self.selectors[selector.0][row] = true;

        Ok(())
    }

    fn query_instance(
        &self,
        column: Column<Instance>,
        row_index: usize,
    ) -> Result<Value<F>, Error> {
        if !self.usable_rows.contains(&row_index) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        self.instance
            .get(column.index())
            .and_then(|column| column.get(row_index))
            .copied()
            .ok_or(Error::BoundsFailure)
    }

    fn assign_advice<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Advice>,
        row_index: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row_index) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        *self
            .advice
            .get_mut(column.index())
            .and_then(|row| row.get_mut(row_index))
            .ok_or(Error::BoundsFailure)? = to().into_field().into_option().map(|x| x.evaluate());

        Ok(())
    }

    fn assign_fixed<V, VR, A, AR>(
        &mut self,
        _: A,
        column: Column<Fixed>,
        row_index: usize,
        to: V,
    ) -> Result<(), Error>
    where
        V: FnOnce() -> Value<VR>,
        VR: Into<Assigned<F>>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row_index) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        *self
            .fixed
            .get_mut(column.index())
            .and_then(|row| row.get_mut(row_index))
            .ok_or(Error::BoundsFailure)? = to().into_field().into_option().map(|x| x.evaluate());

        Ok(())
    }

    fn copy(
        &mut self,
        left_column: Column<Any>,
        left_row: usize,
        right_column: Column<Any>,
        right_row: usize,
    ) -> Result<(), Error> {
        if !self.usable_rows.contains(&left_row) || !self.usable_rows.contains(&right_row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        let copy_constraint = CopyConstraint {
            from_column_type: *left_column.column_type(),
            from_column_index: left_column.index(),
            from_row_index: left_row,
            to_column_type: *right_column.column_type(),
            to_column_index: right_column.index(),
            to_row_index: right_row,
        };
        self.copy_constraints.push(copy_constraint);

        Ok(())
    }

    fn fill_from_row(
        &mut self,
        column: Column<Fixed>,
        from_row: usize,
        to: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        if !self.usable_rows.contains(&from_row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        let col = self
            .fixed
            .get_mut(column.index())
            .ok_or(Error::BoundsFailure)?;

        let filler = to.into_option().map(|x| x.evaluate());
        for row_index in self.usable_rows.clone().skip(from_row) {
            col[row_index] = filler;
        }

        Ok(())
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self, _: Option<String>) {
        // Do nothing; we don't care about namespaces in this context.
    }
}

pub fn dump_gates<F: Field, C: Circuit<F>>() -> Result<Vec<Expression<F>>, Error> {
    let mut meta = ConstraintSystem::default();
    C::configure(&mut meta);

    let gates = meta
        .gates
        .iter()
        .flat_map(|gate| gate.polynomials())
        .cloned()
        .collect();

    Ok(gates)
}

pub fn dump_lookups<F: Field, C: Circuit<F>>() -> Result<Vec<(Expression<F>, Expression<F>)>, Error>
{
    let mut meta = ConstraintSystem::default();
    C::configure(&mut meta);

    let input_expressions = meta
        .lookups
        .iter()
        .flat_map(|argument| argument.input_expressions.iter().cloned());
    let table_expressions = meta
        .lookups
        .iter()
        .flat_map(|argument| argument.table_expressions.iter().cloned());
    let lookup_constraints = input_expressions.zip(table_expressions).collect();

    Ok(lookup_constraints)
}

#[cfg(test)]
mod tests {
    use super::AssignmentDumper;
    use crate::dump::dump_gates;
    use crate::dump::CopyConstraint;
    use crate::plonk::AdviceQuery;
    use crate::plonk::Expression;
    use crate::plonk::FixedQuery;
    use crate::plonk::InstanceQuery;
    use crate::poly::Rotation;

    use crate::circuit::{Layouter, SimpleFloorPlanner, Value};
    use crate::dump::dump_lookups;
    use crate::plonk::TableColumn;
    use crate::plonk::{
        Advice, Any, Circuit, Column, ConstraintSystem, Error, Fixed, FloorPlanner, Instance,
        Selector,
    };
    use pasta_curves::Fp;

    #[derive(Copy, Clone)]
    struct TestConfig {
        a: Column<Fixed>,
        b: Column<Advice>,
        c: Column<Instance>,
        s: Selector,
    }

    struct TestCircuit();

    impl Circuit<Fp> for TestCircuit {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
            let a = meta.fixed_column();
            let b = meta.advice_column();
            let c = meta.instance_column();
            let s = meta.selector();

            Self::Config { a, b, c, s }
        }

        fn without_witnesses(&self) -> Self {
            Self()
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fp>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "region",
                |mut region| {
                    // to test assignment extractions

                    config.s.enable(&mut region, 0)?;
                    region.assign_fixed(|| "", config.a, 0, || Value::known(Fp::from(123)))?;
                    region.assign_advice(|| "", config.b, 0, || Value::known(Fp::from(321)))?;

                    region.assign_fixed(|| "", config.a, 1, || Value::known(Fp::from(456)))?;
                    region.assign_advice(|| "", config.b, 1, || Value::known(Fp::from(654)))?;

                    config.s.enable(&mut region, 2)?;
                    region.assign_fixed(|| "", config.a, 2, || Value::known(Fp::from(789)))?;
                    region.assign_advice(|| "", config.b, 2, || Value::known(Fp::from(987)))?;

                    // to test copy constraint extractions

                    let above =
                        region.assign_advice(|| "", config.b, 3, || Value::known(Fp::from(111)))?;
                    let below =
                        region.assign_advice(|| "", config.b, 4, || Value::known(Fp::from(111)))?;
                    region.constrain_equal(above.cell(), below.cell())?;

                    let left =
                        region.assign_fixed(|| "", config.a, 3, || Value::known(Fp::from(111)))?;
                    region.constrain_equal(left.cell(), above.cell())?;

                    // to test query_instance
                    region.assign_advice_from_instance(|| "", config.c, 0, config.b, 5)?;

                    Ok(())
                },
            )?;

            Ok(())
        }
    }

    #[test]
    fn dump_cells() -> Result<(), Error> {
        let k = 5;
        let mut meta = ConstraintSystem::default();
        let config = TestCircuit::configure(&mut meta);

        let mut cell_dumper: AssignmentDumper<Fp> = AssignmentDumper::new(k, &meta);
        cell_dumper.instance[0][0] = Value::known(Fp::from(777));

        let circuit = TestCircuit();
        <<TestCircuit as Circuit<Fp>>::FloorPlanner as FloorPlanner>::synthesize(
            &mut cell_dumper,
            &circuit,
            config,
            meta.constants.clone(),
        )?;

        assert!(cell_dumper.selectors[0][0]);
        assert_eq!(cell_dumper.fixed[0][0], Some(Fp::from(123)));
        assert_eq!(cell_dumper.advice[0][0], Some(Fp::from(321)));

        assert!(!cell_dumper.selectors[0][1]);
        assert_eq!(cell_dumper.fixed[0][1], Some(Fp::from(456)));
        assert_eq!(cell_dumper.advice[0][1], Some(Fp::from(654)));

        assert!(cell_dumper.selectors[0][2]);
        assert_eq!(cell_dumper.fixed[0][2], Some(Fp::from(789)));
        assert_eq!(cell_dumper.advice[0][2], Some(Fp::from(987)));

        assert_eq!(
            cell_dumper.copy_constraints[0],
            CopyConstraint {
                from_column_type: Any::Advice,
                from_column_index: 0,
                from_row_index: 3,
                to_column_type: Any::Advice,
                to_column_index: 0,
                to_row_index: 4
            }
        );

        assert_eq!(
            cell_dumper.copy_constraints[1],
            CopyConstraint {
                from_column_type: Any::Fixed,
                from_column_index: 0,
                from_row_index: 3,
                to_column_type: Any::Advice,
                to_column_index: 0,
                to_row_index: 3
            }
        );

        assert_eq!(cell_dumper.advice[0][5], Some(Fp::from(777)));

        Ok(())
    }

    #[derive(Copy, Clone)]
    struct LookupTestConfig {
        lookup_table: TableColumn,
        instance: Column<Instance>,
    }

    struct LookupTestCircuit();

    impl Circuit<Fp> for LookupTestCircuit {
        type Config = LookupTestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
            let lookup_table = meta.lookup_table_column();
            let instance = meta.instance_column();

            meta.lookup(|query| {
                let every_instance_cell = query.query_instance(instance, Rotation::cur());
                vec![(every_instance_cell, lookup_table)]
            });

            Self::Config {
                lookup_table,
                instance,
            }
        }

        fn without_witnesses(&self) -> Self {
            Self()
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fp>,
        ) -> Result<(), Error> {
            layouter.assign_table(
                || "",
                |mut region| {
                    region.assign_cell(
                        || "",
                        config.lookup_table,
                        0,
                        || Value::known(Fp::from(111)),
                    )
                },
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_dump_lookups() -> Result<(), Error> {
        let lookup_constraints = dump_lookups::<Fp, LookupTestCircuit>()?;
        assert_eq!(
            lookup_constraints,
            [(
                Expression::Instance(InstanceQuery {
                    index: 0,
                    column_index: 0,
                    rotation: Rotation(0),
                }),
                Expression::Fixed(FixedQuery {
                    index: 0,
                    column_index: 0,
                    rotation: Rotation(0),
                }),
            )]
        );

        Ok(())
    }

    #[derive(Copy, Clone)]
    struct GateTestConfig {
        a: Column<Advice>,
        b: Column<Advice>,
    }

    struct GateTestCircuit();

    impl Circuit<Fp> for GateTestCircuit {
        type Config = GateTestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
            let a = meta.advice_column();
            let b = meta.advice_column();

            meta.create_gate("", |gate| {
                let a_cur = gate.query_advice(a, Rotation::cur());
                let b_cur = gate.query_advice(b, Rotation::cur());
                vec![a_cur * b_cur]
                // One of them has to be 0
            });

            Self::Config { a, b }
        }

        fn without_witnesses(&self) -> Self {
            Self()
        }

        fn synthesize(
            &self,
            _config: Self::Config,
            _layouter: impl Layouter<Fp>,
        ) -> Result<(), Error> {
            Ok(())
        }
    }

    #[test]
    fn test_dump_gates() -> Result<(), Error> {
        let custom_gates = dump_gates::<Fp, GateTestCircuit>()?;
        assert_eq!(
            custom_gates,
            vec![Expression::Product(
                Box::new(Expression::Advice(AdviceQuery {
                    index: 0,
                    column_index: 0,
                    rotation: Rotation(0)
                })),
                Box::new(Expression::Advice(AdviceQuery {
                    index: 1,
                    column_index: 1,
                    rotation: Rotation(0)
                })),
            ),]
        );

        Ok(())
    }
}
