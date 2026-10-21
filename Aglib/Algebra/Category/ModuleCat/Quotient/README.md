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

Closed-immersion descent consumes the original scheme-module stalk
actions and adjunctions.
The existing finite/coherent quotient categories remain specializations;
they are not assumptions of this all-module result.

[Unit](Unit.lean) proves that the original extension/restriction adjunction
unit is surjective, hence an epimorphism, for a surjective commutative ring
map and arbitrary module. It does not assume the source module is annihilated
by the kernel. This is the lower tensor supplier for the geometric quotient
unit.
