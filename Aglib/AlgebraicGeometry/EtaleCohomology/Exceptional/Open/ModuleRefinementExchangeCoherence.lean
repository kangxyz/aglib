/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleCartesianExchangeMate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleIdentityCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleExchangePasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleSourceExchange

/-! # Coherence of the original identity-source Cartesian exchange -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits


universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

/-- The original Cartesian exchange, with its identity direct image removed. -/
def moduleRefinementExchangeIso {U Y X : Scheme.{u}}
    (i : U ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X) [Etale j]
    (h : IsPullback (𝟙 U) i j f) (Λ : Type (u + 1)) [Ring Λ] :
    moduleDirectImage f Λ ⋙ moduleInverseImage j Λ ≅ moduleInverseImage i Λ :=
  SourceChange.adjustedExchangeIso (moduleCartesianExchangeIso (𝟙 U) i j f h Λ)
    (moduleDirectImageIdIso Λ U)

/-- Evaluation retains the original native mate and direct-image identity. -/
theorem moduleRefinementExchangeIso_hom_app {U Y X : Scheme.{u}}
    (i : U ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X) [Etale j]
    (h : IsPullback (𝟙 U) i j f) (Λ : Type (u + 1)) [Ring Λ]
    (M : ModuleSheaf Y Λ) :
    (moduleRefinementExchangeIso i j f h Λ).hom.app M =
      (moduleBaseChangeMap Λ f (𝟙 U) j i h.w).app M ≫
        (moduleDirectImageIdIso Λ U).hom.app ((moduleInverseImage i Λ).obj M) := by
  simp only [moduleRefinementExchangeIso, SourceChange.adjustedExchangeIso_app,
    moduleCartesianExchangeIso_hom]

/-- Original vertical mate pasting after cancelling both identity direct images. -/
theorem moduleBaseChangeMap_identity_source_comp {U Z Y X : Scheme.{u}}
    (i : U ⟶ Z) (j : U ⟶ Y) (l : U ⟶ X) (f : Y ⟶ X) (k : Z ⟶ Y)
    (hf : (𝟙 U) ≫ l = j ≫ f) (hk : (𝟙 U) ≫ j = i ≫ k)
    (ht : (𝟙 U) ≫ l = i ≫ (k ≫ f)) (Λ : Type (u + 1)) [Ring Λ]
    (M : ModuleSheaf Z Λ) :
    (moduleBaseChangeMap Λ (k ≫ f) (𝟙 U) l i ht).app M ≫
        (moduleDirectImageIdIso Λ U).hom.app ((moduleInverseImage i Λ).obj M) =
      (moduleInverseImage l Λ).map ((moduleDirectImageCompIso Λ f k).hom.app M) ≫
        (moduleBaseChangeMap Λ f (𝟙 U) l j hf).app ((moduleDirectImage k Λ).obj M) ≫
        (moduleDirectImageIdIso Λ U).hom.app
          ((moduleInverseImage j Λ).obj ((moduleDirectImage k Λ).obj M)) ≫
        (moduleBaseChangeMap Λ k (𝟙 U) j i hk).app M ≫
        (moduleDirectImageIdIso Λ U).hom.app ((moduleInverseImage i Λ).obj M) := by
  let et : ((𝟙 U) ≫ (𝟙 U)) ≫ l = i ≫ (k ≫ f) :=
    (congrArg (fun a : U ⟶ U => a ≫ l) (Category.id_comp (𝟙 U))).trans ht
  exact SourceChange.identity_source_pasting
    (moduleDirectImage f Λ) (moduleDirectImage k Λ) (moduleDirectImage (k ≫ f) Λ)
    (moduleInverseImage l Λ) (moduleInverseImage j Λ) (moduleInverseImage i Λ)
    (moduleDirectImage (𝟙 U) Λ) (moduleDirectImage ((𝟙 U) ≫ (𝟙 U)) Λ)
    (moduleDirectImageCompIso Λ f k) (moduleDirectImageCompIso Λ (𝟙 U) (𝟙 U))
    (moduleDirectImageIdIso Λ U)
    (eqToIso (congrArg (fun a : U ⟶ U => moduleDirectImage a Λ)
      (Category.comp_id (𝟙 U))))
    (moduleBaseChangeMap Λ f (𝟙 U) l j hf)
    (moduleBaseChangeMap Λ k (𝟙 U) j i hk)
    (moduleBaseChangeMap Λ (k ≫ f) (𝟙 U) l i ht)
    (moduleBaseChangeMap Λ (k ≫ f) ((𝟙 U) ≫ (𝟙 U)) l i et)
    (moduleDirectImageCompIso_id_comp Λ (𝟙 U))
    (moduleBaseChangeMap_vComp Λ f k (𝟙 U) (𝟙 U) l j i hf hk et)
    (SourceChange.indexed_target_transport
      (fun a : U ⟶ U => moduleDirectImage a Λ)
      (moduleDirectImage (k ≫ f) Λ ⋙ moduleInverseImage l Λ) (moduleInverseImage i Λ)
      (fun a : U ⟶ U => a ≫ l = i ≫ (k ≫ f))
      (fun a ha => moduleBaseChangeMap Λ (k ≫ f) a l i ha)
      (Category.comp_id (𝟙 U)) et ht) M

/-- The original source comparison at the identity has its actual inverse component. -/
theorem moduleSourceInverseImageIso_identity_inv_app {U X : Scheme.{u}}
    (i : U ⟶ X) (Λ : Type (u + 1)) [Ring Λ] (M : ModuleSheaf X Λ) :
    (moduleSourceInverseImageIso Λ i (𝟙 U) i (Category.id_comp i)).inv.app M =
      (moduleInverseImageIdIso Λ U).hom.app ((moduleInverseImage i Λ).obj M) := by
  have hs := SourceChange.normalized_source_inverse_app
    (moduleInverseImageCompIso Λ i (𝟙 U)) (moduleInverseImageIdIso Λ U)
    (eqToIso (congrArg (fun a : U ⟶ X => moduleInverseImage a Λ) (Category.id_comp i)))
    (moduleInverseImageCompIso_comp_id Λ i) M
  exact hs

/-- The original identity square mate becomes the inverse-image of the direct identity. -/
theorem moduleBaseChangeMap_identity_source_id {U X : Scheme.{u}}
    (i : U ⟶ X) (h : (𝟙 U) ≫ i = i ≫ (𝟙 X))
    (Λ : Type (u + 1)) [Ring Λ] (M : ModuleSheaf X Λ) :
    (moduleBaseChangeMap Λ (𝟙 X) (𝟙 U) i i h).app M ≫
        (moduleDirectImageIdIso Λ U).hom.app ((moduleInverseImage i Λ).obj M) =
      (moduleInverseImage i Λ).map ((moduleDirectImageIdIso Λ X).hom.app M) := by
  exact SourceChange.identity_source_id
    (moduleInverseImage i Λ) (moduleDirectImage (𝟙 X) Λ)
    (moduleInverseImageAdjunction (𝟙 U) Λ) (moduleDirectImageIdIso Λ X)
    (moduleInverseImageIdIso Λ U) (moduleDirectImageIdIso Λ U)
    (moduleSourceInverseImageIso Λ i (𝟙 U) i (Category.id_comp i))
    (moduleBaseChangeMap Λ (𝟙 X) (𝟙 U) i i h)
    (moduleSourceInverseImageIso_identity_inv_app i Λ)
    (moduleBaseChangeMap_source Λ i (𝟙 U) i (Category.id_comp i))
    (moduleInverseImageIdIso_unit Λ U) M

/-- The adjusted exchange for an identity refinement is the native direct identity. -/
theorem moduleRefinementExchangeIso_id {U X : Scheme.{u}}
    (i : U ⟶ X) [Etale i] (h : IsPullback (𝟙 U) i i (𝟙 X))
    (Λ : Type (u + 1)) [Ring Λ] :
    moduleRefinementExchangeIso i i (𝟙 X) h Λ =
      Functor.isoWhiskerRight (moduleDirectImageIdIso Λ X) (moduleInverseImage i Λ) ≪≫
        Functor.leftUnitor (moduleInverseImage i Λ) := by
  exact SourceChange.adjustedExchangeIso_id
    (moduleInverseImage i Λ) (moduleDirectImage (𝟙 X) Λ)
    (moduleInverseImageAdjunction (𝟙 U) Λ) (moduleDirectImageIdIso Λ X)
    (moduleInverseImageIdIso Λ U) (moduleDirectImageIdIso Λ U)
    (moduleSourceInverseImageIso Λ i (𝟙 U) i (Category.id_comp i))
    (moduleBaseChangeMap Λ (𝟙 X) (𝟙 U) i i h.w)
    (moduleCartesianExchangeIso (𝟙 U) i i (𝟙 X) h Λ)
    (moduleCartesianExchangeIso_hom (𝟙 U) i i (𝟙 X) h Λ)
    (moduleSourceInverseImageIso_identity_inv_app i Λ)
    (moduleBaseChangeMap_source Λ i (𝟙 U) i (Category.id_comp i))
    (moduleInverseImageIdIso_unit Λ U)

/-- Composition of identity-source exchanges uses the original direct-image comparison. -/
theorem moduleRefinementExchangeIso_comp {U Z Y X : Scheme.{u}}
    (i : U ⟶ Z) (j : U ⟶ Y) (l : U ⟶ X) (f : Y ⟶ X) (k : Z ⟶ Y)
    [Etale j] [Etale l]
    (hf : IsPullback (𝟙 U) j l f) (hk : IsPullback (𝟙 U) i j k)
    (ht : IsPullback (𝟙 U) i l (k ≫ f)) (Λ : Type (u + 1)) [Ring Λ] :
    moduleRefinementExchangeIso i l (k ≫ f) ht Λ =
      Functor.isoWhiskerRight (moduleDirectImageCompIso Λ f k) (moduleInverseImage l Λ) ≪≫
        Functor.associator (moduleDirectImage k Λ) (moduleDirectImage f Λ)
          (moduleInverseImage l Λ) ≪≫
        Functor.isoWhiskerLeft (moduleDirectImage k Λ)
          (moduleRefinementExchangeIso j l f hf Λ) ≪≫
        moduleRefinementExchangeIso i j k hk Λ := by
  let et : ((𝟙 U) ≫ (𝟙 U)) ≫ l = i ≫ (k ≫ f) :=
    (congrArg (fun a : U ⟶ U => a ≫ l) (Category.id_comp (𝟙 U))).trans ht.w
  exact SourceChange.adjustedExchangeIso_comp
    (moduleDirectImage f Λ) (moduleDirectImage k Λ) (moduleDirectImage (k ≫ f) Λ)
    (moduleInverseImage l Λ) (moduleInverseImage j Λ) (moduleInverseImage i Λ)
    (moduleDirectImage (𝟙 U) Λ) (moduleDirectImage ((𝟙 U) ≫ (𝟙 U)) Λ)
    (moduleDirectImageCompIso Λ f k) (moduleDirectImageCompIso Λ (𝟙 U) (𝟙 U))
    (moduleDirectImageIdIso Λ U)
    (eqToIso (congrArg (fun a : U ⟶ U => moduleDirectImage a Λ)
      (Category.comp_id (𝟙 U))))
    (moduleBaseChangeMap Λ f (𝟙 U) l j hf.w)
    (moduleBaseChangeMap Λ k (𝟙 U) j i hk.w)
    (moduleBaseChangeMap Λ (k ≫ f) (𝟙 U) l i ht.w)
    (moduleBaseChangeMap Λ (k ≫ f) ((𝟙 U) ≫ (𝟙 U)) l i et)
    (moduleCartesianExchangeIso (𝟙 U) j l f hf Λ)
    (moduleCartesianExchangeIso (𝟙 U) i j k hk Λ)
    (moduleCartesianExchangeIso (𝟙 U) i l (k ≫ f) ht Λ)
    (moduleCartesianExchangeIso_hom (𝟙 U) j l f hf Λ)
    (moduleCartesianExchangeIso_hom (𝟙 U) i j k hk Λ)
    (moduleCartesianExchangeIso_hom (𝟙 U) i l (k ≫ f) ht Λ)
    (moduleDirectImageCompIso_id_comp Λ (𝟙 U))
    (moduleBaseChangeMap_vComp Λ f k (𝟙 U) (𝟙 U) l j i hf.w hk.w et)
    (SourceChange.indexed_target_transport
      (fun a : U ⟶ U => moduleDirectImage a Λ)
      (moduleDirectImage (k ≫ f) Λ ⋙ moduleInverseImage l Λ) (moduleInverseImage i Λ)
      (fun a : U ⟶ U => a ≫ l = i ≫ (k ≫ f))
      (fun a ha => moduleBaseChangeMap Λ (k ≫ f) a l i ha)
      (Category.comp_id (𝟙 U)) et ht.w)

end AlgebraicGeometry.Scheme.EtaleCohomology
