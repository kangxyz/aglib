/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleInverseImageCoherence
public import Aglib.CategoryTheory.Adjunction.Mates.SelectedUnitValues

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
  exact CategoryTheory.SelectedAdjointUnit.unit_app
    (moduleInverseImageAdjunction (𝟙 X) Λ) Adjunction.id (moduleDirectImageIdIso Λ X) M

/-- The original native inverse-image identity is the mate of the native direct identity. -/
theorem conjugateEquiv_moduleInverseImageIdIso_hom (X : Scheme.{u}) :
    conjugateEquiv Adjunction.id (moduleInverseImageAdjunction (𝟙 X) Λ)
      (moduleInverseImageIdIso Λ X).hom = (moduleDirectImageIdIso Λ X).inv := by
  exact conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    (moduleInverseImageAdjunction (𝟙 X) Λ) Adjunction.id (moduleDirectImageIdIso Λ X)

/-- The identity inverse-image comparison retains the original adjunction counit. -/
theorem moduleInverseImageIdIso_counit (X : Scheme.{u}) (M : ModuleSheaf X Λ) :
    (moduleInverseImageAdjunction (𝟙 X) Λ).counit.app M =
      (moduleInverseImageIdIso Λ X).hom.app ((moduleDirectImage (𝟙 X) Λ).obj M) ≫
        (moduleDirectImageIdIso Λ X).hom.app M := by
  exact CategoryTheory.SelectedAdjointUnit.identity_counit_app
    (moduleInverseImageAdjunction (𝟙 X) Λ) (moduleDirectImageIdIso Λ X) M

/-- The native inverse-image comparison with the source identity is normalized. -/
theorem moduleInverseImageCompIso_comp_id {X S : Scheme.{u}} (f : S ⟶ X) :
    moduleInverseImageCompIso Λ f (𝟙 S) ≪≫
        Functor.isoWhiskerLeft (moduleInverseImage f Λ) (moduleInverseImageIdIso Λ S) ≪≫
        Functor.rightUnitor (moduleInverseImage f Λ) =
      eqToIso (congrArg (fun k : S ⟶ X => moduleInverseImage k Λ) (Category.id_comp f)) := by
  exact CategoryTheory.SelectedAdjointCoherence.comp_id_of_right
    (fun k : S ⟶ X => moduleInverseImage k Λ)
    (fun k : S ⟶ X => moduleDirectImage k Λ) (fun k => moduleInverseImageAdjunction k Λ)
    (moduleInverseImageAdjunction (𝟙 S) Λ) (Category.id_comp f)
    (moduleInverseImageCompIso Λ f (𝟙 S)) (moduleDirectImageCompIso Λ f (𝟙 S)).symm
    (moduleInverseImageIdIso Λ S) (moduleDirectImageIdIso Λ S)
    (conjugateEquiv_moduleInverseImageCompIso_hom Λ f (𝟙 S))
    (conjugateEquiv_moduleInverseImageIdIso_hom Λ S) (moduleDirectImageCompIso_comp_id Λ f)

/-- The native inverse-image comparison with the target identity is normalized. -/
theorem moduleInverseImageCompIso_id_comp {X S : Scheme.{u}} (f : S ⟶ X) :
    moduleInverseImageCompIso Λ (𝟙 X) f ≪≫
        Functor.isoWhiskerRight (moduleInverseImageIdIso Λ X) (moduleInverseImage f Λ) ≪≫
        Functor.leftUnitor (moduleInverseImage f Λ) =
      eqToIso (congrArg (fun k : S ⟶ X => moduleInverseImage k Λ) (Category.comp_id f)) := by
  exact CategoryTheory.SelectedAdjointCoherence.id_comp_of_right
    (fun k : S ⟶ X => moduleInverseImage k Λ)
    (fun k : S ⟶ X => moduleDirectImage k Λ) (fun k => moduleInverseImageAdjunction k Λ)
    (moduleInverseImageAdjunction (𝟙 X) Λ) (Category.comp_id f)
    (moduleInverseImageCompIso Λ (𝟙 X) f) (moduleDirectImageCompIso Λ (𝟙 X) f).symm
    (moduleInverseImageIdIso Λ X) (moduleDirectImageIdIso Λ X)
    (conjugateEquiv_moduleInverseImageCompIso_hom Λ (𝟙 X) f)
    (conjugateEquiv_moduleInverseImageIdIso_hom Λ X) (moduleDirectImageCompIso_id_comp Λ f)


end AlgebraicGeometry.Scheme.EtaleCohomology
