/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleComparisons
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap
public import Aglib.CategoryTheory.Adjunction.Mates.SelectedUnitValues

/-! # Original native module composition maps on sections and adjunction units -/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients
open CategoryTheory.TorsionZMod.Ringed

attribute [local instance] hasSheafifyRingStandard hasSheafifyAbStandard
  ringWEqualsLocallyBijectiveStandard abWEqualsLocallyBijectiveStandard hasSheafifyModules

variable {X S T : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ] (f : S ⟶ X) (g : T ⟶ S)

/-- The native direct-image composition retains the original chart map on every section. -/
theorem moduleDirectImageCompIso_inv_app_apply (M : ModuleSheaf T Λ) (U : X.Etaleᵒᵖ)
    (x : M.val.obj (op ((siteBaseChange g).obj ((siteBaseChange f).obj U.unop)))) :
    (((moduleDirectImageCompIso Λ f g).inv.app M).val.app U) x =
      M.val.map (((siteBaseChangeComp f g).hom.app U.unop).op) x := by
  exact ModuleCat.Sheaf.ConstantRing.moduleDirectImageCompIso_inv_app_apply.{
    u + 1, u, u + 1, u, u + 1, u, u + 1, u + 1}
    (siteBaseChange f) (siteBaseChange g) (siteBaseChange (g ≫ f))
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
    (Scheme.smallEtaleTopology T) Λ (siteBaseChangeComp f g).symm M U x

/-- Native inverse-image composition retains the original composite adjunction unit. -/
@[reassoc]
theorem moduleInverseImageCompIso_unit (M : ModuleSheaf X Λ) :
    (moduleInverseImageAdjunction (g ≫ f) Λ).unit.app M ≫
      (moduleDirectImage (g ≫ f) Λ).map ((moduleInverseImageCompIso Λ f g).hom.app M) ≫
      (moduleDirectImageCompIso Λ f g).hom.app
        ((moduleInverseImage g Λ).obj ((moduleInverseImage f Λ).obj M)) =
    ((moduleInverseImageAdjunction f Λ).comp (moduleInverseImageAdjunction g Λ)).unit.app M := by
  rw [moduleInverseImageCompIso_eq_original]
  exact CategoryTheory.SelectedAdjointUnit.unit_app
    (moduleInverseImageAdjunction (g ≫ f) Λ)
    ((moduleInverseImageAdjunction f Λ).comp (moduleInverseImageAdjunction g Λ))
    (moduleDirectImageCompIso Λ f g) M

end AlgebraicGeometry.Scheme.EtaleCohomology
