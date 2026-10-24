/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleInverseImageCoherence

/-! # Original identity normalizations for native module images -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable (Λ : Type (u + 1)) [Ring Λ]

/-- The native direct-image identity has the original underlying identity comparison. -/
theorem moduleDirectImageIdIso_inv_underlying (X : Scheme.{u}) (M : ModuleSheaf X Λ) :
    (SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).map
      ((moduleDirectImageIdIso Λ X).inv.app M) =
    (directImageIdIso X).inv.app
      ((SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).obj M) := by
  let W := (Functor.whiskeringRight (ModuleSheaf X Λ) (ModuleSheaf X Λ)
    (ModuleValuedSheaf X Λ)).obj (moduleSheafEquivalence X Λ).inverse
  have h := W.map_preimage (moduleDirectImageIdValuedIso Λ X).inv
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  ext x
  exact congrArg (fun a => (((a.app M).hom.app U).hom x)) h

/-- Equality transport retains its original underlying direct-image map. -/
theorem moduleDirectImage_eqToHom_underlying {X S : Scheme.{u}}
    {f g : S ⟶ X} (h : f = g) (M : ModuleSheaf S Λ) :
    (SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).map
      ((eqToHom (congrArg (fun k => moduleDirectImage k Λ) h)).app M) =
    (eqToHom (congrArg (fun k => directImage k) h)).app
      ((SheafOfModules.toSheaf.{u + 1} (constantRing S Λ)).obj M) := by
  subst g
  simp only [eqToHom_refl, NatTrans.id_app]
  exact (SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).map_id
    ((moduleDirectImage f Λ).obj M)

/-- Native direct-image composition with the source identity is normalized. -/
theorem moduleDirectImageCompIso_comp_id {X S : Scheme.{u}} (f : S ⟶ X) :
    moduleDirectImageCompIso Λ f (𝟙 S) ≪≫
        Functor.isoWhiskerRight (moduleDirectImageIdIso Λ S) (moduleDirectImage f Λ) ≪≫
        Functor.leftUnitor (moduleDirectImage f Λ) =
      eqToIso (congrArg (fun k : S ⟶ X => moduleDirectImage k Λ) (Category.id_comp f)) := by
  apply Iso.ext_inv
  apply NatTrans.ext
  funext M
  apply (SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).map_injective
  have h := congrArg (fun e : directImage (𝟙 S ≫ f) ≅ directImage f => e.inv.app
    ((SheafOfModules.toSheaf.{u + 1} (constantRing S Λ)).obj M))
    (directImageCompIso_comp_id f)
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Category.id_comp, eqToIso.inv,
    Functor.map_comp, moduleDirectImage_underlying_map,
    moduleDirectImageCompIso_inv_underlying, moduleDirectImageIdIso_inv_underlying,
    moduleDirectImage_eqToHom_underlying] at h ⊢
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  ext x
  exact congrArg (fun a => (a.hom.app U) x) h

/-- Native direct-image composition with the target identity is normalized. -/
theorem moduleDirectImageCompIso_id_comp {X S : Scheme.{u}} (f : S ⟶ X) :
    moduleDirectImageCompIso Λ (𝟙 X) f ≪≫
        Functor.isoWhiskerLeft (moduleDirectImage f Λ) (moduleDirectImageIdIso Λ X) ≪≫
        Functor.rightUnitor (moduleDirectImage f Λ) =
      eqToIso (congrArg (fun k : S ⟶ X => moduleDirectImage k Λ) (Category.comp_id f)) := by
  apply Iso.ext_inv
  apply NatTrans.ext
  funext M
  apply (SheafOfModules.toSheaf.{u + 1} (constantRing X Λ)).map_injective
  have h := congrArg (fun e : directImage (f ≫ 𝟙 X) ≅ directImage f => e.inv.app
    ((SheafOfModules.toSheaf.{u + 1} (constantRing S Λ)).obj M))
    (directImageCompIso_id_comp f)
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.rightUnitor_inv_app, Category.id_comp, eqToIso.inv,
    Functor.map_comp,
    moduleDirectImageCompIso_inv_underlying, moduleDirectImageIdIso_inv_underlying] at h ⊢
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  ext x
  exact congrArg (fun a => (a.hom.app U) x) h

/-- The identity inverse-image comparison retains the original adjunction unit. -/
theorem moduleInverseImageIdIso_unit (X : Scheme.{u}) (M : ModuleSheaf X Λ) :
    (moduleInverseImageAdjunction (𝟙 X) Λ).unit.app M ≫
      (moduleDirectImage (𝟙 X) Λ).map ((moduleInverseImageIdIso Λ X).hom.app M) ≫
        (moduleDirectImageIdIso Λ X).hom.app M = 𝟙 M := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((moduleInverseImageAdjunction (𝟙 X) Λ).ofNatIsoRight
      (moduleDirectImageIdIso Λ X)) Adjunction.id M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit] at h
  change ((moduleInverseImageAdjunction (𝟙 X) Λ).unit.app M ≫
      (moduleDirectImage (𝟙 X) Λ).map ((moduleInverseImageIdIso Λ X).hom.app M)) ≫
      (moduleDirectImageIdIso Λ X).hom.app M = 𝟙 M at h
  exact (Category.assoc _ _ _).symm.trans h

/-- The original native inverse-image identity is the mate of the native direct identity. -/
theorem conjugateEquiv_moduleInverseImageIdIso_hom (X : Scheme.{u}) :
    conjugateEquiv Adjunction.id (moduleInverseImageAdjunction (𝟙 X) Λ)
      (moduleInverseImageIdIso Λ X).hom = (moduleDirectImageIdIso Λ X).inv := by
  apply NatTrans.ext
  funext M
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((moduleInverseImageAdjunction (𝟙 X) Λ).ofNatIsoRight
      (moduleDirectImageIdIso Λ X)) Adjunction.id M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit] at h
  change ((moduleInverseImageAdjunction (𝟙 X) Λ).unit.app M ≫
      (moduleDirectImage (𝟙 X) Λ).map ((moduleInverseImageIdIso Λ X).hom.app M)) ≫
      (moduleDirectImageIdIso Λ X).hom.app M = 𝟙 M at h
  have hc := unit_conjugateEquiv Adjunction.id (moduleInverseImageAdjunction (𝟙 X) Λ)
    (moduleInverseImageIdIso Λ X).hom M
  change (𝟙 M) ≫ _ = _ at hc
  simp only [Category.id_comp, Functor.id_obj] at hc
  apply (cancel_mono ((moduleDirectImageIdIso Λ X).hom.app M)).1
  rw [hc, Iso.inv_hom_id_app]
  exact h

/-- The identity inverse-image comparison retains the original adjunction counit. -/
theorem moduleInverseImageIdIso_counit (X : Scheme.{u}) (M : ModuleSheaf X Λ) :
    (moduleInverseImageAdjunction (𝟙 X) Λ).counit.app M =
      (moduleInverseImageIdIso Λ X).hom.app ((moduleDirectImage (𝟙 X) Λ).obj M) ≫
        (moduleDirectImageIdIso Λ X).hom.app M := by
  have hc := conjugateEquiv_counit Adjunction.id
    (moduleInverseImageAdjunction (𝟙 X) Λ) (moduleInverseImageIdIso Λ X).hom M
  rw [conjugateEquiv_moduleInverseImageIdIso_hom] at hc
  change (moduleInverseImage (𝟙 X) Λ).map ((moduleDirectImageIdIso Λ X).inv.app M) ≫
      (moduleInverseImageAdjunction (𝟙 X) Λ).counit.app M =
    (moduleInverseImageIdIso Λ X).hom.app M ≫ 𝟙 M at hc
  have hn := (moduleInverseImageIdIso Λ X).hom.naturality
    ((moduleDirectImageIdIso Λ X).inv.app M)
  apply (cancel_epi ((moduleInverseImage (𝟙 X) Λ).map
    ((moduleDirectImageIdIso Λ X).inv.app M))).1
  rw [hc, ← Category.assoc, hn]
  simp only [Functor.id_map, Functor.id_obj, Category.assoc, Iso.inv_hom_id_app]

/-- The native inverse-image comparison with the source identity is normalized. -/
theorem moduleInverseImageCompIso_comp_id {X S : Scheme.{u}} (f : S ⟶ X) :
    moduleInverseImageCompIso Λ f (𝟙 S) ≪≫
        Functor.isoWhiskerLeft (moduleInverseImage f Λ) (moduleInverseImageIdIso Λ S) ≪≫
        Functor.rightUnitor (moduleInverseImage f Λ) =
      eqToIso (congrArg (fun k : S ⟶ X => moduleInverseImage k Λ) (Category.id_comp f)) := by
  let af := moduleInverseImageAdjunction f Λ
  let ai := moduleInverseImageAdjunction (𝟙 S) Λ
  let atotal := moduleInverseImageAdjunction (𝟙 S ≫ f) Λ
  have hc : conjugateEquiv af atotal
      ((moduleInverseImageCompIso Λ f (𝟙 S)).hom ≫
        Functor.whiskerLeft (moduleInverseImage f Λ) (moduleInverseImageIdIso Λ S).hom ≫
        (Functor.rightUnitor (moduleInverseImage f Λ)).hom) =
      (Functor.leftUnitor (moduleDirectImage f Λ)).inv ≫
        Functor.whiskerRight (moduleDirectImageIdIso Λ S).inv (moduleDirectImage f Λ) ≫
        (moduleDirectImageCompIso Λ f (𝟙 S)).inv := by
    rw [← conjugateEquiv_comp _ (af.comp ai),
      ← conjugateEquiv_comp _ (af.comp Adjunction.id),
      conjugateEquiv_rightUnitor_hom, conjugateEquiv_whiskerLeft,
      conjugateEquiv_moduleInverseImageIdIso_hom, conjugateEquiv_moduleInverseImageCompIso_hom]
    simp only [Category.assoc]
  apply Iso.ext
  apply (conjugateEquiv af atotal).injective
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, eqToIso.hom]
  rw [hc, conjugateEquiv_moduleInverseImage_eqToHom Λ (Category.id_comp f)]
  simpa only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv,
    eqToIso.inv, Category.assoc] using congrArg Iso.inv (moduleDirectImageCompIso_comp_id Λ f)

/-- The native inverse-image comparison with the target identity is normalized. -/
theorem moduleInverseImageCompIso_id_comp {X S : Scheme.{u}} (f : S ⟶ X) :
    moduleInverseImageCompIso Λ (𝟙 X) f ≪≫
        Functor.isoWhiskerRight (moduleInverseImageIdIso Λ X) (moduleInverseImage f Λ) ≪≫
        Functor.leftUnitor (moduleInverseImage f Λ) =
      eqToIso (congrArg (fun k : S ⟶ X => moduleInverseImage k Λ) (Category.comp_id f)) := by
  let af := moduleInverseImageAdjunction f Λ
  let ai := moduleInverseImageAdjunction (𝟙 X) Λ
  let atotal := moduleInverseImageAdjunction (f ≫ 𝟙 X) Λ
  have hc : conjugateEquiv af atotal
      ((moduleInverseImageCompIso Λ (𝟙 X) f).hom ≫
        Functor.whiskerRight (moduleInverseImageIdIso Λ X).hom (moduleInverseImage f Λ) ≫
        (Functor.leftUnitor (moduleInverseImage f Λ)).hom) =
      (Functor.rightUnitor (moduleDirectImage f Λ)).inv ≫
        Functor.whiskerLeft (moduleDirectImage f Λ) (moduleDirectImageIdIso Λ X).inv ≫
        (moduleDirectImageCompIso Λ (𝟙 X) f).inv := by
    rw [← conjugateEquiv_comp _ (ai.comp af),
      ← conjugateEquiv_comp _ (Adjunction.id.comp af),
      conjugateEquiv_leftUnitor_hom, conjugateEquiv_whiskerRight,
      conjugateEquiv_moduleInverseImageIdIso_hom, conjugateEquiv_moduleInverseImageCompIso_hom]
    simp only [Category.assoc]
  apply Iso.ext
  apply (conjugateEquiv af atotal).injective
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, eqToIso.hom]
  rw [hc, conjugateEquiv_moduleInverseImage_eqToHom Λ (Category.comp_id f)]
  simpa only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    eqToIso.inv, Category.assoc] using congrArg Iso.inv (moduleDirectImageCompIso_id_comp Λ f)


end AlgebraicGeometry.Scheme.EtaleCohomology
