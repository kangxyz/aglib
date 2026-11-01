/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleScalarRestrictionValuedMate

/-! # The original chart-restriction lower-shriek scalar unit -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- The original chart restriction identification is literal, including its adjunction unit. -/
theorem moduleValuedLowerShriekRestrictionAdjunction_eq_comp
    (R : Type (u + 1)) [Ring R] :
    moduleValuedLowerShriekRestrictionAdjunction j R =
      (moduleEtaleSliceSheafEquivalence j R).toAdjunction.comp
        (Sheaf.SliceCohomology.lowerShriekAdjunction (Scheme.smallEtaleTopology X)
          (ModuleCat.{u + 1} R) (Scheme.Etale.mk j)) := by
  apply Adjunction.ext
  apply NatTrans.ext
  funext M
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

variable {Λ Γ : Type (u + 1)} [Ring Λ] [Ring Γ] (φ : Λ →+* Γ)

/-- The original module-valued lower-shriek/chart adjunction retains the literal scalar mate. -/
theorem moduleValuedLowerShriekRestriction_scalar_mate :
    (mateEquiv (moduleValuedLowerShriekRestrictionAdjunction j Γ)
      (moduleValuedLowerShriekRestrictionAdjunction j Λ)
      (TwoSquare.mk _ _ _ _ (moduleValuedLowerShriekScalarRestrictionIso j φ).inv)).natTrans =
    𝟙 (moduleValuedEtaleRestriction j Γ ⋙ moduleValuedRestrictScalars U φ) := by
  rw [moduleValuedLowerShriekRestrictionAdjunction_eq_comp,
    moduleValuedLowerShriekRestrictionAdjunction_eq_comp]
  exact moduleValuedLowerShriekScalarRestriction_composite_mate j φ

/-- The old module-valued lower-shriek scalar comparison preserves the original
chart-restriction adjunction unit. -/
@[reassoc]
theorem moduleValuedLowerShriekRestriction_scalar_unit (M : ModuleValuedSheaf U Γ) :
    (moduleValuedRestrictScalars U φ).map
        ((moduleValuedLowerShriekRestrictionAdjunction j Γ).unit.app M) ≫
      (moduleValuedEtaleRestriction j Λ).map
        ((moduleValuedLowerShriekScalarRestrictionIso j φ).hom.app M) =
    (moduleValuedLowerShriekRestrictionAdjunction j Λ).unit.app
      ((moduleValuedRestrictScalars U φ).obj M) := by
  have h := unit_mateEquiv (moduleValuedLowerShriekRestrictionAdjunction j Γ)
    (moduleValuedLowerShriekRestrictionAdjunction j Λ)
    (TwoSquare.mk _ _ _ _ (moduleValuedLowerShriekScalarRestrictionIso j φ).inv) M
  change (moduleValuedRestrictScalars U φ).map
      ((moduleValuedLowerShriekRestrictionAdjunction j Γ).unit.app M) ≫
      (mateEquiv (moduleValuedLowerShriekRestrictionAdjunction j Γ)
        (moduleValuedLowerShriekRestrictionAdjunction j Λ)
        (TwoSquare.mk _ _ _ _ (moduleValuedLowerShriekScalarRestrictionIso j φ).inv)).natTrans.app
          ((moduleValuedLowerShriek j Γ).obj M) =
    (moduleValuedLowerShriekRestrictionAdjunction j Λ).unit.app
      ((moduleValuedRestrictScalars U φ).obj M) ≫
      (moduleValuedEtaleRestriction j Λ).map
        ((moduleValuedLowerShriekScalarRestrictionIso j φ).inv.app M) at h
  rw [moduleValuedLowerShriekRestriction_scalar_mate] at h
  have he := (Category.comp_id _).symm.trans h
  have hc := congrArg (fun k => k ≫ (moduleValuedEtaleRestriction j Λ).map
    ((moduleValuedLowerShriekScalarRestrictionIso j φ).hom.app M)) he
  have hi := ((moduleValuedEtaleRestriction j Λ).mapIso
    ((moduleValuedLowerShriekScalarRestrictionIso j φ).app M)).inv_hom_id
  exact hc.trans ((Category.assoc _ _ _).trans
    ((congrArg (fun k => (moduleValuedLowerShriekRestrictionAdjunction j Λ).unit.app
      ((moduleValuedRestrictScalars U φ).obj M) ≫ k) hi).trans (Category.comp_id _)))

end AlgebraicGeometry.Scheme.EtaleCohomology
