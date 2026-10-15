# Finite modules and scalar constructions

`ModuleCat.finiteModule` and `ModuleCat.FiniteModule` in [Finite](Finite.lean) are the actual finite-generation property and full subcategory of modules over a ring. Ring and module-object universes may differ. The essential-smallness bound is the ring universe; the abelian/Serre structure and `finiteModuleExactStructure` require `IsNoetherianRing`.

| Result/interface | Exact conditions and mathematical content |
| --- | --- |
| `ModuleCat.FiniteRestrictionScalars.moduleRestriction` / `moduleRestrictionExact` | Restriction of the actual action along a finite ring map preserves finite generation. The exact-category interface keeps the stated Noetherian source/target assumptions. |
| `ModuleCat.FiniteLocalization.functor`, `torsion_iff_elementwise`, `torsion_iff_uniform` | For a commutative ring and arbitrary submonoid, actual localization defines a kernel property. Finite generation equates elementwise denominator torsion with a uniform denominator. Finite-limit/Serre interfaces retain Noetherianity. |
| `ModuleCat.FiniteLocalization.IdealClosedSupport.closedEquivalence` | Actual finite modules over `R/I` are equivalent to finite `R`-modules killed by every element of `I`. This is not power torsion and is not asserted extension-closed. |
| `ModuleCat.restrictedExtensionUnit_apply` | For compatible commutative ring maps `R → A → S`, the restricted extension/restriction unit is literally `x ↦ 1 ⊗ x`. The compatibility equality of scalar maps remains an input. |

Focused imports are `Aglib.Algebra.Category.ModuleCat.Finite`, [FiniteRestrictionScalars](FiniteRestrictionScalars.lean), [FiniteLocalization](FiniteLocalization.lean), [IdealClosedSupport](IdealClosedSupport.lean) and [ScalarExtensionUnit](ScalarExtensionUnit.lean). The ideal-killed exact restriction/inclusion keeps its stated abelian-structure premises.

[Localization/Exactness](Localization/README.md) is the lower actual-localization detection interface. [Affine finite-type quasicoherent sheaves](../../../AlgebraicGeometry/Modules/QuasiCoherent/Affine/README.md), finite direct image and closed-immersion module actions are the geometric consumers. [Abelian subcategories](../../../CategoryTheory/Abelian/Subcategory/README.md) and [exact structures](../../../CategoryTheory/ExactCategory/README.md) provide the categorical layer.

The latest generic lower interfaces add [ChangeOfRings](ChangeOfRings/README.md), [Monoidal scalar restriction](Monoidal/README.md), [scalar-extension tensor](Tensor/README.md), [module presheaves](Presheaf/README.md) and [site module sheaves](Sheaf/README.md). The site tensor is canonical below scheme and invertible sheaves; finite-free/retract exactness and injective preservation are separate properties.

[FinitePresentation](FinitePresentation.lean) proves finite presentation of
the actual categorical cokernel of a map from a finite module to a
finitely presented module. Ring and carrier universes remain independent.
The proof transfers the native quotient presentation through the original
cokernel/range-quotient isomorphism. Free-locus and Grauert arguments use
this lower result without imposing Noetherianity.
