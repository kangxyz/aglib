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
