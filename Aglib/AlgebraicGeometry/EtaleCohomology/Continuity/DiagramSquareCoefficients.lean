/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap

/-! # Original coefficient maps across commutative scheme squares -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

private lemma inverse_pasting {C : Type*} [Category C]
    {U V R T W : C} (a : T ≅ W) (b : R ≅ T) (c : U ≅ V)
    (p : U ⟶ R) (l : V ⟶ W)
    (h : p ≫ b.hom ≫ a.hom = c.hom ≫ l) :
    l ≫ a.inv ≫ b.inv = c.inv ≫ p := by
  have ht := congrArg (fun k : U ⟶ W => c.inv ≫ k ≫ a.inv ≫ b.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc,
    Category.comp_id] using ht.symm

/-- The native square isomorphism transports a coefficient transition. -/
def squareCoefficientMap {X₀ S₀ X₁ S₁ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (g : S₁ ⟶ S₀) (h : X₁ ⟶ X₀)
    (e : f₁ ≫ g = h ≫ f₀)
    {F : AbelianSheaf.{u, u + 1} S₀} {G : AbelianSheaf.{u, u + 1} S₁}
    (φ : (inverseImage g).obj F ⟶ G) :
    (inverseImage h).obj ((inverseImage f₀).obj F) ⟶ (inverseImage f₁).obj G :=
  (inverseImageSquareIso f₀ f₁ g h e).inv.app F ≫ (inverseImage f₁).map φ

section Horizontal
variable {X₀ S₀ X₁ S₁ X₂ S₂ : Scheme.{u}}
  (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
  (g₁ : S₁ ⟶ S₀) (g₂ : S₂ ⟶ S₁) (h₁ : X₁ ⟶ X₀) (h₂ : X₂ ⟶ X₁)
  (e₁ : f₁ ≫ g₁ = h₁ ≫ f₀) (e₂ : f₂ ≫ g₂ = h₂ ≫ f₁)
  (e : f₂ ≫ (g₂ ≫ g₁) = (h₂ ≫ h₁) ≫ f₀)

/-- Inverse form of the already proved original square-pasting equation. -/
lemma inverseImageSquareIso_inv_hComp (F : AbelianSheaf.{u, u + 1} S₀) :
    (inverseImageComp h₁ h₂).hom.app ((inverseImage f₀).obj F) ≫
        (inverseImage h₂).map ((inverseImageSquareIso f₀ f₁ g₁ h₁ e₁).inv.app F) ≫
        (inverseImageSquareIso f₁ f₂ g₂ h₂ e₂).inv.app ((inverseImage g₁).obj F) =
      (inverseImageSquareIso f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).inv.app F ≫
        (inverseImage f₂).map ((inverseImageComp g₁ g₂).hom.app F) := by
  let a := (inverseImage h₂).mapIso ((inverseImageSquareIso f₀ f₁ g₁ h₁ e₁).app F)
  let b := (inverseImageSquareIso f₁ f₂ g₂ h₂ e₂).app ((inverseImage g₁).obj F)
  let c := (inverseImageSquareIso f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).app F
  exact inverse_pasting a b c _ _
    (inverseImageSquareIso_hComp f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e F)

/-- Two native coefficient-square maps compose with the original inverse-image comparisons. -/
lemma squareCoefficientMap_hComp
    {F : AbelianSheaf.{u, u + 1} S₀} {G : AbelianSheaf.{u, u + 1} S₁}
    {H : AbelianSheaf.{u, u + 1} S₂}
    (φ : (inverseImage g₁).obj F ⟶ G) (ψ : (inverseImage g₂).obj G ⟶ H) :
    (inverseImageComp h₁ h₂).hom.app ((inverseImage f₀).obj F) ≫
        (inverseImage h₂).map (squareCoefficientMap f₀ f₁ g₁ h₁ e₁ φ) ≫
        squareCoefficientMap f₁ f₂ g₂ h₂ e₂ ψ =
      squareCoefficientMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e
        ((inverseImageComp g₁ g₂).hom.app F ≫ (inverseImage g₂).map φ ≫ ψ) := by
  have hn := (inverseImageSquareIso f₁ f₂ g₂ h₂ e₂).inv.naturality φ
  simp only [Functor.comp_map] at hn
  have hp := inverseImageSquareIso_inv_hComp f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e F
  dsimp only [squareCoefficientMap]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((inverseImage h₂).map ((inverseImage f₁).map φ)), hn]
  have ht := congrArg
    (fun k : (inverseImage (h₂ ≫ h₁)).obj ((inverseImage f₀).obj F) ⟶
        (inverseImage f₂).obj ((inverseImage g₂).obj ((inverseImage g₁).obj F)) =>
      k ≫ (inverseImage f₂).map ((inverseImage g₂).map φ) ≫ (inverseImage f₂).map ψ) hp
  simpa only [Category.assoc] using ht

end Horizontal
end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
