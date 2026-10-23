/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramArrowSections

/-! # Original square transport for a specified compatible coefficient system -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X)

/-- Transport sections across the specified commuting square using the original
system transition. -/
def systemSquareSectionsMap {i j : I} (a : i ⟶ j) {Y Z : Scheme.{u}}
    (f : Y ⟶ (X.obj i).unop) (g : Z ⟶ (X.obj j).unop) (h : Z ⟶ Y)
    (e : g ≫ (X.map a).unop = h ≫ f) :
    (globalSections Y).obj ((inverseImage f).obj (F.obj i)) ⟶
      (globalSections Z).obj ((inverseImage g).obj (F.obj j)) :=
  squareSectionsMap f g (X.map a).unop h e (diagramInverseTransition X F a)

lemma systemSquareSectionsMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k)
    {Y₀ Y₁ Y₂ : Scheme.{u}} (f₀ : Y₀ ⟶ (X.obj i).unop)
    (f₁ : Y₁ ⟶ (X.obj j).unop) (f₂ : Y₂ ⟶ (X.obj k).unop)
    (h₁ : Y₁ ⟶ Y₀) (h₂ : Y₂ ⟶ Y₁) (t : Y₂ ⟶ Y₀) (et : t = h₂ ≫ h₁)
    (e₁ : f₁ ≫ (X.map a).unop = h₁ ≫ f₀)
    (e₂ : f₂ ≫ (X.map b).unop = h₂ ≫ f₁)
    (e : f₂ ≫ (X.map (a ≫ b)).unop = t ≫ f₀) :
    systemSquareSectionsMap X F (a ≫ b) f₀ f₂ t e =
      systemSquareSectionsMap X F a f₀ f₁ h₁ e₁ ≫
        systemSquareSectionsMap X F b f₁ f₂ h₂ e₂ := by
  dsimp only [systemSquareSectionsMap]
  rw [diagramInverseTransition_comp]
  simp only [diagramInverseImageComp, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app]
  let e' : f₂ ≫ ((X.map b).unop ≫ (X.map a).unop) = (h₂ ≫ h₁) ≫ f₀ := by
    rw [← Category.assoc, e₂, Category.assoc, e₁, ← Category.assoc]
  let φ : (inverseImage ((X.map b).unop ≫ (X.map a).unop)).obj (F.obj i) ⟶ F.obj k :=
    (inverseImageComp (X.map a).unop (X.map b).unop).hom.app (F.obj i) ≫
      (inverseImage (X.map b).unop).map (diagramInverseTransition X F a) ≫
        diagramInverseTransition X F b
  have ht := squareSectionsMap_transport f₀ f₂
    ((X.map b).unop ≫ (X.map a).unop) (X.map (a ≫ b)).unop
    (h₂ ≫ h₁) t
    (congrArg (fun s : X.obj i ⟶ X.obj k => s.unop) (X.map_comp a b)) et e' e φ
  have hp := squareSectionsMap_hComp f₀ f₁ f₂ (X.map a).unop (X.map b).unop
    h₁ h₂ e₁ e₂ e' (diagramInverseTransition X F a) (diagramInverseTransition X F b)
  exact ht.trans hp.symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
