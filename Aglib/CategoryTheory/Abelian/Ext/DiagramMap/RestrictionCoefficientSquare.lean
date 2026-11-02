/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.CoefficientSquare

/-! # Complete original Ext coefficient and open-restriction squares

The original open-Ext diagrams, global Ext objects, exact transfers,
coefficient arrows and top comparison are constructed before native sheaf
specialization. Both coefficient and top naturality are proved there; the
original open-comparison normalization is the remaining input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w

namespace CategoryTheory

/-- Assemble all original open, coefficient and whole-space comparison maps
and their square over variable diagrams, before native module specialization. -/
def openRestrictionCoefficientSquare
    {I J : Type*} [Category* I] [Category* J]
    (R : I ⥤ J) (P : I ⥤ AddCommGrpCat.{w}) (A B : J ⥤ AddCommGrpCat.{w})
    (g₀ : P ⟶ R ⋙ A) (g₁ : P ⟶ R ⋙ B) (θ : A ⟶ B)
    (hpost : g₁ = g₀ ≫ Functor.whiskerLeft R θ)
    (i : I) (j : J) (κ : R.obj i ⟶ j)
    {HA HB : AddCommGrpCat.{w}} (topA : A.obj j ⟶ HA) (topB : B.obj j ⟶ HB)
    (f : HA ⟶ HB) (htop : ∀ y, topB (θ.app j y) = f (topA y))
    (openMap : P.obj i ⟶ HA)
    (hopen : ∀ y, openMap y = topA (A.map κ (g₀.app i y))) :
    Square AddCommGrpCat.{w} where
  X₁ := P.obj i
  X₂ := HA
  X₃ := B.obj j
  X₄ := HB
  f₁₂ := openMap
  f₂₄ := f
  f₁₃ := g₁.app i ≫ B.map κ
  f₃₄ := topB
  fac := by
    have htop' : θ.app j ≫ topB = topA ≫ f := by
      ext y
      exact htop y
    have hopen' : openMap = g₀.app i ≫ A.map κ ≫ topA := by
      ext y
      exact hopen y
    calc
      openMap ≫ f = g₀.app i ≫ A.map κ ≫ topA ≫ f := by
        rw [hopen', Category.assoc, Category.assoc]
      _ = g₀.app i ≫ A.map κ ≫ θ.app j ≫ topB := by rw [← htop']
      _ = g₀.app i ≫ θ.app (R.obj i) ≫ B.map κ ≫ topB := by
        simpa only [Category.assoc] using
          congrArg (fun z => g₀.app i ≫ z ≫ topB) (θ.naturality κ)
      _ = (g₁.app i ≫ B.map κ) ≫ topB := by
        simp only [hpost, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]

end CategoryTheory

namespace CategoryTheory.Functor

universe i j k l u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w} D]
  {I : Type i} [Category.{j} I] {J : Type k} [Category.{l} J]

/-- Construct every original Ext object and map, and both naturality laws,
before specializing the coefficient and open-restriction comparison. -/
def extDiagramOpenRestrictionCoefficientSquare
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (F : I ⥤ C) (G : J ⥤ D) (H : I ⥤ J) (e : F ⋙ L ≅ H ⋙ G)
    {A : C} {B B' : D} (φ : L.obj A ⟶ B) (φ' : L.obj A ⟶ B')
    (ψ : B ⟶ B') (hφ : φ' = φ ≫ ψ) (n : ℕ)
    (i : Iᵒᵖ) (j : Jᵒᵖ) (κ : H.op.obj i ⟶ j)
    (Z : D) (t : G.obj j.unop ≅ Z)
    (openMap : ((F.op ⋙ extFunctor n).flip.obj A).obj i ⟶
      ((extFunctor n).obj (op Z)).obj B) :
    (∀ x, openMap x = (((extFunctor n).mapIso t.op).inv.app B)
      (((G.op ⋙ extFunctor n).flip.obj B).map κ
        ((L.extDiagramMap F (H ⋙ G) e φ n).app i x))) → Square AddCommGrpCat.{w} := by
  intro hopen
  let P := (F.op ⋙ extFunctor n).flip.obj A
  let Q := (G.op ⋙ extFunctor n).flip.obj B
  let Q' := (G.op ⋙ extFunctor n).flip.obj B'
  let g₀ := L.extDiagramMap F (H ⋙ G) e φ n
  let g₁ := L.extDiagramMap F (H ⋙ G) e φ' n
  let θ := (G.op ⋙ extFunctor n).flip.map ψ
  let top := ((extFunctor n).mapIso t.op).symm
  have hc : L.map (𝟙 A) ≫ φ' = φ ≫ ψ := by
    simpa only [Functor.map_id, Category.id_comp] using hφ
  have hp : g₁ = g₀ ≫ Functor.whiskerLeft H.op θ := by
    simpa only [Functor.map_id, Category.id_comp] using
      L.extDiagramMap_coefficients F G H e φ φ' (𝟙 A) ψ hc n
  exact openRestrictionCoefficientSquare H.op P Q Q' g₀ g₁ θ hp i j κ
    (top.hom.app B) (top.hom.app B') (((extFunctor n).obj (op Z)).map ψ)
    (fun x => ConcreteCategory.congr_hom (top.hom.naturality ψ) x) openMap hopen

end CategoryTheory.Functor
