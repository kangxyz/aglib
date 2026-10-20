# Finitely generated module categories

[Basic](Basic.lean), imported as `Aglib.Algebra.Category.FGModuleCat.Basic`, extends
Mathlib's actual `FGModuleCat R`. `ModuleCat.finiteModule` is the native finite-
generation property, and `ModuleCat.FiniteModule` abbreviates this same category.
Ring and module-object universes may differ; essential smallness is bounded by
the ring universe. The Serre/abelian structure and `finiteModuleExactStructure`
retain `IsNoetherianRing R`.

[RestrictScalars](RestrictScalars.lean) preserves finite generation along a finite
commutative ring map. Its selected exact-category functor retains the stated
Noetherian source and target assumptions. [Localization](Localization.lean)
uses an arbitrary submonoid of a commutative ring: finite generation identifies
elementwise denominator torsion with uniform denominator torsion. Its finite-
limit and Serre interfaces retain their Noetherian hypotheses.

[IdealClosedSupport](IdealClosedSupport.lean) identifies actual finite modules
over `R/I` with finite `R`-modules killed by each element of `I`. This is ideal
annihilation; the guide asserts no extension closure or power-torsion replacement.
The selected restriction/inclusion keeps its stated abelian-structure premises.

Lower [module localization](../ModuleCat/Localization/README.md),
[abelian subcategories](../../../CategoryTheory/Abelian/Subcategory/README.md) and
[exact structures](../../../CategoryTheory/ExactCategory/README.md) supply the
algebraic and categorical interfaces. Current geometric consumers are
[affine finite-type quasicoherent sheaves](../../../AlgebraicGeometry/Modules/QuasiCoherent/Affine/README.md),
finite direct image and closed-immersion module actions. General scalar, tensor
and site constructions remain in [ModuleCat](../ModuleCat/README.md).

The [localization family](Localization/README.md) adds arbitrary-ring essential
surjectivity and the Noetherian torsion Serre quotient equivalence for the actual
finite-module localization functor.

[ScalarExtension](ScalarExtension.lean) defines `FGModuleCat.finiteModuleExtension` using the literal
`ModuleCat.extendScalars` on the existing finite-module category. Its finite-limit
and exact interfaces retain flatness and the displayed Noetherian source and
target hypotheses. `fieldModuleExtensionExact` uses flatness over a field and
requires no finiteness condition on that field extension.

[PrincipalMultiplication](PrincipalMultiplication.lean) constructs the original multiplication/quotient short
complex. In a Noetherian domain, a nonzero scalar gives its actual short exact
sequence; its quotient is killed by principal localization. [ScalarAutomorphisms](ScalarAutomorphisms.lean)
compares unit multiplication through the canonical rank-one tensor and
localization isomorphisms. The specified scalar map and localized-unit equality
remain explicit.

[ScalarMatrices](ScalarMatrices.lean) identifies actual matrix automorphisms with the native finite
module maps. For a finite-dimensional field algebra and a supplied basis it proves
the restriction-of-scalars square and conjugacy using the existing
`FiniteRestrictionScalars.moduleRestriction`. This has no separability premise.
Its matrices and determinants come from `LinearAlgebra.Matrix.ScalarRestriction`.
