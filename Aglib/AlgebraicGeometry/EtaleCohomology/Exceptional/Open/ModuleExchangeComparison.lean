/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleAdjunctionCompatibility

/-! # The original chart exchange under the coefficient equivalence -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) [Etale g]
  (Λ : Type (u + 1)) [Ring Λ]

/-- The actual native chart exchange satisfies its defining valued comparison square. -/
@[reassoc]
theorem moduleEtaleBaseChangeIso_valued (M : ModuleSheaf X Λ) :
    (moduleSheafEquivalence T Λ).inverse.map
        ((moduleEtaleBaseChangeIso f g Λ).hom.app M) ≫
      (moduleDirectImageComparison (pullback.fst g f) Λ).hom.app
        ((moduleInverseImage (pullback.snd g f) Λ).obj M) ≫
      (moduleValuedDirectImage (pullback.fst g f) Λ).map
        ((moduleInverseImageValuedIso Λ (pullback.snd g f)).hom.app M) =
    (moduleInverseImageValuedIso Λ g).hom.app ((moduleDirectImage f Λ).obj M) ≫
      (moduleValuedInverseImage g Λ).map ((moduleDirectImageComparison f Λ).hom.app M) ≫
      (moduleValuedEtaleBaseChangeIso f g Λ).hom.app
        ((moduleSheafEquivalence X Λ).inverse.obj M) := by
  let W := (Functor.whiskeringRight (ModuleSheaf X Λ) (ModuleSheaf T Λ)
    (ModuleValuedSheaf T Λ)).obj (moduleSheafEquivalence T Λ).inverse
  have h := W.map_preimage (moduleEtaleBaseChangeValuedIso f g Λ).hom
  have hc := congrArg (fun a => a.app M ≫
    (moduleEtaleBaseChangeRightIso f g Λ).hom.app M) h
  change (moduleSheafEquivalence T Λ).inverse.map
      ((moduleEtaleBaseChangeIso f g Λ).hom.app M) ≫
        (moduleEtaleBaseChangeRightIso f g Λ).hom.app M = _ at hc
  simp only [moduleEtaleBaseChangeValuedIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hc
  simp only [moduleEtaleBaseChangeRightIso, moduleEtaleBaseChangeLeftIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Category.id_comp, Category.comp_id, Functor.comp_obj,
    Category.assoc] at hc
  exact hc.trans (Category.id_comp _)

end AlgebraicGeometry.Scheme.EtaleCohomology
