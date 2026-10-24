/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleDirectImageCoherence

/-! # Native inverse-image composition and its original adjunction mate -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable (Λ : Type (u + 1)) [Ring Λ]

/-- Native inverse-image composition is exactly the mate of native direct-image composition. -/
theorem conjugateEquiv_moduleInverseImageCompIso_hom {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) :
    conjugateEquiv ((moduleInverseImageAdjunction f Λ).comp
        (moduleInverseImageAdjunction g Λ)) (moduleInverseImageAdjunction (g ≫ f) Λ)
      (moduleInverseImageCompIso Λ f g).hom = (moduleDirectImageCompIso Λ f g).inv := by
  let a := moduleInverseImageAdjunction (g ≫ f) Λ
  let b := (moduleInverseImageAdjunction f Λ).comp (moduleInverseImageAdjunction g Λ)
  apply (conjugateEquiv b a).symm.injective
  rw [Equiv.symm_apply_apply]
  apply NatTrans.ext
  funext M
  apply (a.homEquiv _ _).injective
  have h := moduleInverseImageCompIso_unit Λ f g M
  have hu := unit_conjugateEquiv_symm b a (moduleDirectImageCompIso Λ f g).inv M
  change a.unit.app M ≫ _ = _
  apply (cancel_mono ((moduleDirectImageCompIso Λ f g).hom.app
    ((moduleInverseImage g Λ).obj ((moduleInverseImage f Λ).obj M)))).mp
  change (a.unit.app M ≫ _) ≫ _ = (a.unit.app M ≫ _) ≫ _
  rw [Category.assoc, h, ← hu]
  simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rfl

/-- Equality transport for native inverse images has the reversed original direct-image mate. -/
theorem conjugateEquiv_moduleInverseImage_eqToHom {X S : Scheme.{u}} {f g : S ⟶ X}
    (h : f = g) :
    conjugateEquiv (moduleInverseImageAdjunction g Λ) (moduleInverseImageAdjunction f Λ)
        (eqToHom (congrArg (fun k : S ⟶ X => moduleInverseImage k Λ) h)) =
      eqToHom (congrArg (fun k : S ⟶ X => moduleDirectImage k Λ) h.symm) := by
  subst g
  simp

/-- Native inverse-image composition associates with its original base-map transport. -/
theorem moduleInverseImageCompIso_assoc {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) :
    moduleInverseImageCompIso Λ f (h ≫ g) ≪≫
        Functor.isoWhiskerLeft (moduleInverseImage f Λ) (moduleInverseImageCompIso Λ g h) =
      eqToIso (congrArg (fun k : V ⟶ X => moduleInverseImage k Λ) (Category.assoc h g f)) ≪≫
        moduleInverseImageCompIso Λ (g ≫ f) h ≪≫
        Functor.isoWhiskerRight (moduleInverseImageCompIso Λ f g) (moduleInverseImage h Λ) ≪≫
        Functor.associator (moduleInverseImage f Λ)
          (moduleInverseImage g Λ) (moduleInverseImage h Λ) := by
  let af := moduleInverseImageAdjunction f Λ
  let ag := moduleInverseImageAdjunction g Λ
  let ah := moduleInverseImageAdjunction h Λ
  let afg := moduleInverseImageAdjunction (g ≫ f) Λ
  let agh := moduleInverseImageAdjunction (h ≫ g) Λ
  let adjTotal := moduleInverseImageAdjunction ((h ≫ g) ≫ f) Λ
  let adjTotalAssoc := moduleInverseImageAdjunction (h ≫ (g ≫ f)) Λ
  have hL : conjugateEquiv (af.comp (ag.comp ah)) adjTotal
      ((moduleInverseImageCompIso Λ f (h ≫ g)).hom ≫
        Functor.whiskerLeft (moduleInverseImage f Λ) (moduleInverseImageCompIso Λ g h).hom) =
      Functor.whiskerRight (moduleDirectImageCompIso Λ g h).inv (moduleDirectImage f Λ) ≫
        (moduleDirectImageCompIso Λ f (h ≫ g)).inv := by
    rw [← conjugateEquiv_comp _ (af.comp agh), conjugateEquiv_whiskerLeft]
    rw [conjugateEquiv_moduleInverseImageCompIso_hom,
      conjugateEquiv_moduleInverseImageCompIso_hom]
  have hR : conjugateEquiv (af.comp (ag.comp ah)) adjTotal
      (eqToHom (congrArg (fun k : V ⟶ X => moduleInverseImage k Λ) (Category.assoc h g f)) ≫
        (moduleInverseImageCompIso Λ (g ≫ f) h).hom ≫
        Functor.whiskerRight (moduleInverseImageCompIso Λ f g).hom (moduleInverseImage h Λ) ≫
        (Functor.associator (moduleInverseImage f Λ)
          (moduleInverseImage g Λ) (moduleInverseImage h Λ)).hom) =
      (Functor.associator (moduleDirectImage h Λ)
        (moduleDirectImage g Λ) (moduleDirectImage f Λ)).hom ≫
        Functor.whiskerLeft (moduleDirectImage h Λ) (moduleDirectImageCompIso Λ f g).inv ≫
        (moduleDirectImageCompIso Λ (g ≫ f) h).inv ≫
        eqToHom (congrArg (fun k : V ⟶ X => moduleDirectImage k Λ)
          (Category.assoc h g f).symm) := by
    rw [← conjugateEquiv_comp _ adjTotalAssoc, ← conjugateEquiv_comp _ (afg.comp ah),
      ← conjugateEquiv_comp _ ((af.comp ag).comp ah),
      conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight]
    rw [conjugateEquiv_moduleInverseImageCompIso_hom,
      conjugateEquiv_moduleInverseImageCompIso_hom, conjugateEquiv_moduleInverseImage_eqToHom]
    all_goals simp only [Category.assoc]
  apply Iso.ext
  apply (conjugateEquiv (af.comp (ag.comp ah)) adjTotal).injective
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    eqToIso.hom]
  rw [hL, hR]
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_app]
  apply (cancel_mono (eqToIso
    (congrArg (fun k => (moduleDirectImage k Λ).obj M) (Category.assoc h g f))).hom).mp
  simpa only [Category.assoc, eqToIso.hom, eqToHom_trans, eqToHom_refl,
    Category.comp_id] using moduleDirectImageCompIso_assoc_app Λ f g h M

end AlgebraicGeometry.Scheme.EtaleCohomology
