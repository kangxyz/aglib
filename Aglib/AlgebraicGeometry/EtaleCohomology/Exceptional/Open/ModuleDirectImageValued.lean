/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleExchangeMate

/-! # Original direct-image composition under the coefficient equivalence -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {X S T : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ]
  (f : S ⟶ X) (g : T ⟶ S)

/-- The native composition comparison is the original valued comparison after transport. -/
@[reassoc]
theorem moduleDirectImageCompIso_hom_valued (M : ModuleSheaf T Λ) :
    (moduleSheafEquivalence X Λ).inverse.map
        ((moduleDirectImageCompIso Λ f g).hom.app M) ≫
      (moduleDirectImageCompRightIso Λ f g).hom.app M =
    (moduleDirectImageComparison (g ≫ f) Λ).hom.app M ≫
      (moduleValuedDirectImageCompIso Λ f g).hom.app
        ((moduleSheafEquivalence T Λ).inverse.obj M) := by
  let W := (Functor.whiskeringRight (ModuleSheaf T Λ) (ModuleSheaf X Λ)
    (ModuleValuedSheaf X Λ)).obj (moduleSheafEquivalence X Λ).inverse
  have h := W.map_preimage
    (moduleDirectImageComparison (g ≫ f) Λ ≪≫
      Functor.isoWhiskerLeft _ (moduleValuedDirectImageCompIso Λ f g) ≪≫
      (moduleDirectImageCompRightIso Λ f g).symm).hom
  have hc := congrArg (fun a => a.app M ≫
    (moduleDirectImageCompRightIso Λ f g).hom.app M) h
  change (moduleSheafEquivalence X Λ).inverse.map
      ((moduleDirectImageCompIso Λ f g).hom.app M) ≫
      (moduleDirectImageCompRightIso Λ f g).hom.app M = _ at hc
  simpa only [
    Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using hc

end AlgebraicGeometry.Scheme.EtaleCohomology
