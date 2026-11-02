/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSquareCoefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackCohomologySystem

/-! # Actual global-section transport across coefficient squares -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

lemma squareCoefficientMap_id {X S : Scheme.{u}} (f : X ⟶ S)
    (e : f ≫ 𝟙 S = 𝟙 X ≫ f) (F : AbelianSheaf.{u, u + 1} S) :
    squareCoefficientMap f f (𝟙 S) (𝟙 X) e ((inverseImageId S).hom.app F) =
      (inverseImageId X).hom.app ((inverseImage f).obj F) := by
  have hc := congrArg (fun z => z.hom.app F) (inverseImageSquareIso_id f e)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app] at hc
  change (inverseImageSquareIso f f (𝟙 S) (𝟙 X) e).hom.app F ≫
      (inverseImageId X).hom.app ((inverseImage f).obj F) ≫
        𝟙 ((inverseImage f).obj F) =
    (inverseImage f).map ((inverseImageId S).hom.app F) ≫
      𝟙 ((inverseImage f).obj F) at hc
  let m : (inverseImage (𝟙 X)).obj ((inverseImage f).obj F) ⟶
      (inverseImage f).obj F := (inverseImageId X).hom.app ((inverseImage f).obj F)
  let n : (inverseImage f).obj ((inverseImage (𝟙 S)).obj F) ⟶
      (inverseImage f).obj F := (inverseImage f).map ((inverseImageId S).hom.app F)
  have hc' : (inverseImageSquareIso f f (𝟙 S) (𝟙 X) e).hom.app F ≫ m = n :=
    (congrArg
      (fun k : (inverseImage (𝟙 X)).obj ((inverseImage f).obj F) ⟶
          (inverseImage f).obj F =>
        (inverseImageSquareIso f f (𝟙 S) (𝟙 X) e).hom.app F ≫ k)
      (Category.comp_id m)).symm.trans (hc.trans (Category.comp_id n))
  have ht := congrArg
    (fun k => (inverseImageSquareIso f f (𝟙 S) (𝟙 X) e).inv.app F ≫ k) hc'
  simpa only [squareCoefficientMap, ← Category.assoc, Iso.inv_hom_id_app,
    Category.id_comp, m, n] using ht.symm

/-- Pullback on sections followed by the original coefficient square. -/
def squareSectionsMap {X₀ S₀ X₁ S₁ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (g : S₁ ⟶ S₀) (h : X₁ ⟶ X₀)
    (e : f₁ ≫ g = h ≫ f₀)
    {F : AbelianSheaf.{u, u + 1} S₀} {G : AbelianSheaf.{u, u + 1} S₁}
    (φ : (inverseImage g).obj F ⟶ G) :
    (globalSections X₀).obj ((inverseImage f₀).obj F) ⟶
      (globalSections X₁).obj ((inverseImage f₁).obj G) :=
  globalSectionsPullback h ((inverseImage f₀).obj F) ≫
    (globalSections X₁).map (squareCoefficientMap f₀ f₁ g h e φ)

lemma squareSectionsMap_id {X S : Scheme.{u}} (f : X ⟶ S)
    (e : f ≫ 𝟙 S = 𝟙 X ≫ f) (F : AbelianSheaf.{u, u + 1} S) :
    squareSectionsMap f f (𝟙 S) (𝟙 X) e ((inverseImageId S).hom.app F) = 𝟙 _ := by
  dsimp only [squareSectionsMap]
  rw [squareCoefficientMap_id, globalSectionsPullback_id]

lemma squareSectionsMap_hComp {X₀ S₀ X₁ S₁ X₂ S₂ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
    (g₁ : S₁ ⟶ S₀) (g₂ : S₂ ⟶ S₁) (h₁ : X₁ ⟶ X₀) (h₂ : X₂ ⟶ X₁)
    (e₁ : f₁ ≫ g₁ = h₁ ≫ f₀) (e₂ : f₂ ≫ g₂ = h₂ ≫ f₁)
    (e : f₂ ≫ (g₂ ≫ g₁) = (h₂ ≫ h₁) ≫ f₀)
    {F : AbelianSheaf.{u, u + 1} S₀} {G : AbelianSheaf.{u, u + 1} S₁}
    {H : AbelianSheaf.{u, u + 1} S₂}
    (φ : (inverseImage g₁).obj F ⟶ G) (ψ : (inverseImage g₂).obj G ⟶ H) :
    squareSectionsMap f₀ f₁ g₁ h₁ e₁ φ ≫ squareSectionsMap f₁ f₂ g₂ h₂ e₂ ψ =
      squareSectionsMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e
        ((inverseImageComp g₁ g₂).hom.app F ≫ (inverseImage g₂).map φ ≫ ψ) := by
  dsimp only [squareSectionsMap]
  simp only [Category.assoc]
  rw [globalSectionsPullback_naturality_assoc, ← globalSectionsPullback_comp_assoc]
  simp only [← Functor.map_comp]
  rw [squareCoefficientMap_hComp f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e]

/-- Equality transports on the two horizontal maps preserve the original section map. -/
lemma squareSectionsMap_transport {X₀ S₀ X₁ S₁ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (g g' : S₁ ⟶ S₀) (h h' : X₁ ⟶ X₀)
    (eg : g' = g) (eh : h' = h)
    (e : f₁ ≫ g = h ≫ f₀) (e' : f₁ ≫ g' = h' ≫ f₀)
    {F : AbelianSheaf.{u, u + 1} S₀} {G : AbelianSheaf.{u, u + 1} S₁}
    (φ : (inverseImage g).obj F ⟶ G) :
    squareSectionsMap f₀ f₁ g' h' e'
      (eqToHom (congrArg (fun k : S₁ ⟶ S₀ => (inverseImage k).obj F) eg) ≫ φ) =
        squareSectionsMap f₀ f₁ g h e φ := by
  subst g'
  subst h'
  simp only [eqToHom_refl, Category.id_comp]

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
