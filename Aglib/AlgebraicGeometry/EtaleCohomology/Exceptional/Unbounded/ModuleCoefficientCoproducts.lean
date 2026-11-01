/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CoefficientCoproducts
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CohomologicalBound
public import
  Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Coproducts.CoefficientComparison
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-! # Original module higher direct images preserve coefficient coproducts

The same-degree underlying comparison is natural in all original coefficient
maps. Actual scalar forgetting preserves colimits and reflects their universal
property. No faithfulness of a derived coefficient functor is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wMX wMS wAX wAS

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable (Λ : Type (u + 1)) [Ring Λ] {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]

/-- The original higher-image underlying comparison is a natural isomorphism,
not only a collection of isomorphisms of coefficient objects. -/
def moduleHigherDirectImageUnderlyingIso (n : ℕ) :
    (moduleDirectImage f Λ).rightDerived n ⋙ SheafOfModules.toSheaf (constantRing S Λ) ≅
      SheafOfModules.toSheaf (constantRing X Λ) ⋙ higherDirectImage f n :=
  Functor.rightDerivedExactCoefficientIso (moduleDirectImage f Λ) (directImage f)
    (SheafOfModules.toSheaf (constantRing X Λ)) (SheafOfModules.toSheaf (constantRing S Λ))
    (moduleDerivedDirectImageUnderlyingIso Λ f) n

/-- Every component is the already normalized original object comparison. -/
theorem moduleHigherDirectImageUnderlyingIso_app (n : ℕ) (M : ModuleSheaf X Λ) :
    (moduleHigherDirectImageUnderlyingIso Λ f n).app M =
      moduleHigherDirectImageUnderlyingObjIso Λ f M n := rfl

/-- All original module higher direct images under a qcqs morphism preserve
arbitrary coproducts in the coefficient universe. -/
theorem moduleRightDerived_preservesCoproducts [QuasiCompact f] [QuasiSeparated f]
    (n : ℕ) (κ : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete κ) ((moduleDirectImage f Λ).rightDerived n) := by
  let U := SheafOfModules.toSheaf (constantRing X Λ)
  let V := SheafOfModules.toSheaf (constantRing S Λ)
  let : PreservesColimitsOfShape (Discrete κ) (higherDirectImage f n) :=
    Continuity.higherDirectImage_preservesCoproducts f n κ
  let : PreservesColimitsOfShape (Discrete κ) (U ⋙ higherDirectImage f n) := inferInstance
  let : PreservesColimitsOfShape (Discrete κ) (((moduleDirectImage f Λ).rightDerived n) ⋙ V) :=
    preservesColimitsOfShape_of_natIso (moduleHigherDirectImageUnderlyingIso Λ f n).symm
  let : ReflectsColimitsOfShape (Discrete κ) V := reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves ((moduleDirectImage f Λ).rightDerived n) V

/-- The original ordinary module direct image preserves the same coproducts;
this is transported through the original degree-zero derived comparison. -/
theorem moduleDirectImage_preservesCoproducts [QuasiCompact f] [QuasiSeparated f]
    (κ : Type (u + 1)) : PreservesColimitsOfShape (Discrete κ) (moduleDirectImage f Λ) := by
  let : PreservesColimitsOfShape (Discrete κ) ((moduleDirectImage f Λ).rightDerived 0) :=
    moduleRightDerived_preservesCoproducts Λ f 0 κ
  exact preservesColimitsOfShape_of_natIso (moduleDirectImage f Λ).rightDerivedZeroIsoSelf

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
