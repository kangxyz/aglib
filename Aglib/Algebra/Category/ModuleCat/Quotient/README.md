# Actual module descent through a ring quotient

Import `Aglib.Algebra.Category.ModuleCat.Quotient.Descent`.
`ModuleCat.fullyFaithfulRestrictScalarsOfSurjective` proves full
faithfulness of the native restriction functor along a surjective ring
map, on arbitrary modules. The rings and module carriers have independent
universes. The actual original linear maps are the preimages.

`ker_le_annihilator_restrictScalars` and
`mem_essImage_restrictScalars_iff_ker_le_annihilator` identify its essential
image with exactly the modules annihilated by the original kernel. The
proof supplies the actual quotient action using the native
`Module.IsTorsionBySet.module` and the native first isomorphism theorem.
These results hold for rings without commutativity or finiteness assumptions.

For commutative rings,
`extendRestrictScalarsAdj_counit_isIso_of_surjective` proves invertibility
of the original native adjunction counit.
`extendRestrictScalarsAdj_unit_isIso_iff_ker_le_annihilator` characterizes
invertibility of its original unit by the same annihilator condition.
The native adjunction's module carrier has universe `max v w`, where `w`
is the target-ring universe; the source-ring universe stays independent.
There is no flatness or finite-generation hypothesis.

The leaf passed alone through the shared guarded wrapper with receipt
`1792110237867749000-51660`. Its geometric consumer uses the original
scheme-module stalk actions and adjunctions for closed-immersion descent.
The existing finite/coherent quotient categories remain specializations;
they are not assumptions of this all-module result.

The independent `QuotientModuleDescentConsumer.lean` passed with receipt
`1792110351874146000-53287`. It checks unrelated ring and module-carrier
universes, noncommutative ring restriction, and the original commutative
scalar unit/counit criteria. All five inspected declarations use only the
three standard axioms; the fully faithful constructor and kernel action
formula do not need classical choice.
