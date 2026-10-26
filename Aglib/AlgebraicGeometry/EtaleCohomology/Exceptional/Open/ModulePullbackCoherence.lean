/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleComparisons
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap

/-! # Original native module composition maps on sections and adjunction units -/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {X S T : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ] (f : S ⟶ X) (g : T ⟶ S)

/-- The native direct-image composition retains the original chart map on every section. -/
theorem moduleDirectImageCompIso_inv_app_apply (M : ModuleSheaf T Λ) (U : X.Etaleᵒᵖ)
    (x : M.val.obj (op ((siteBaseChange g).obj ((siteBaseChange f).obj U.unop)))) :
    (((moduleDirectImageCompIso Λ f g).inv.app M).val.app U) x =
      M.val.map (((siteBaseChangeComp f g).hom.app U.unop).op) x := by
  let W := (Functor.whiskeringRight (ModuleSheaf T Λ) (ModuleSheaf X Λ)
    (ModuleValuedSheaf X Λ)).obj (moduleSheafEquivalence X Λ).inverse
  have h := W.map_preimage
    (moduleDirectImageComparison (g ≫ f) Λ ≪≫
      Functor.isoWhiskerLeft _ (moduleValuedDirectImageCompIso Λ f g) ≪≫
      (moduleDirectImageCompRightIso Λ f g).symm).inv
  exact congrArg (fun a => (((a.app M).hom.app U).hom x)) h

/-- Native inverse-image composition retains the original composite adjunction unit. -/
@[reassoc]
theorem moduleInverseImageCompIso_unit (M : ModuleSheaf X Λ) :
    (moduleInverseImageAdjunction (g ≫ f) Λ).unit.app M ≫
      (moduleDirectImage (g ≫ f) Λ).map ((moduleInverseImageCompIso Λ f g).hom.app M) ≫
      (moduleDirectImageCompIso Λ f g).hom.app
        ((moduleInverseImage g Λ).obj ((moduleInverseImage f Λ).obj M)) =
    ((moduleInverseImageAdjunction f Λ).comp (moduleInverseImageAdjunction g Λ)).unit.app M := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((moduleInverseImageAdjunction (g ≫ f) Λ).ofNatIsoRight
      (moduleDirectImageCompIso Λ f g))
    ((moduleInverseImageAdjunction f Λ).comp (moduleInverseImageAdjunction g Λ)) M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  rw [moduleInverseImageCompIso_eq_original]
  simpa only [Adjunction.homEquiv_unit, Functor.comp_obj, Category.assoc] using h

end AlgebraicGeometry.Scheme.EtaleCohomology
