# Finite length and scalar restriction

[Restriction](Restriction.lean), imported as
`Aglib.Algebra.Category.ModuleCat.FiniteLength.Restriction`, supplies two separate
transport results. `ModuleCat.localizedModule_surjective_of_units` proves
surjectivity of a supplied actual module-localization map when every denominator
is a unit. `ModuleCat.finiteLength_restrictScalars` preserves finite length under
the native restriction functor along a surjective map of commutative rings.

The first result permits independent ring and module-carrier universes. The
second retains the source's common ring/module universe. A denominator-unit
condition is not inferred from finite length. The native
[finite-length support](../../../../RingTheory/FiniteLength/README.md) interface
remains the lower module-theoretic owner.
