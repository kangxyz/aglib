# Algebraic module categories

The [ModuleCat](ModuleCat/README.md) family owns arbitrary module categories, scalar restriction, localization and quotient-ring actions. Its [localization exactness](ModuleCat/Localization/README.md) detects exactness through compatible actual localizations at elements spanning the unit ideal. [FGModuleCat](FGModuleCat/README.md) separately owns finitely generated module categories and their guarded Serre/exact structures. [Ring](Ring/README.md) owns canonical localization maps in `CommRingCat`.

These algebraic objects feed the [affine quasicoherent comparison](../../AlgebraicGeometry/Modules/QuasiCoherent/Affine/README.md). An equivalence with sheaves uses the actual tilde/global-section maps; an exact-functor result uses the selected [categorical exact structure](../../CategoryTheory/ExactCategory/README.md).

[ProjectiveInt](Grp/ProjectiveInt.lean) gives the single proof of projectivity of
`AddCommGrpCat.of (ULift ℤ)` by lifting its integer generator. Terminal-site and
finite local-component constant-sheaf arguments reuse this source.
[TupleCoordinates](Grp/Products/TupleCoordinates.lean) constructs dependent
additive reindexing and coordinate isomorphisms. Its full value equation
`t ≫ b.hom = a.hom ≫ E.hom` proves invertibility of the original arrow, including
transport through an existing source isomorphism, with independent coefficient
and index universes and no finite-index premise.
