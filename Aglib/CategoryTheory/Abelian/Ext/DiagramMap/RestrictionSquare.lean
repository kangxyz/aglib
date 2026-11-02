/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap
public import Mathlib.CategoryTheory.Square

/-! # Complete original Ext-diagram restriction squares

All four original diagrams and exact-transfer families are constructed over
variable abelian categories. Index evaluation, original index transport and
the whole comparison law are assembled at that same level, before any native
site or module coefficient specialization. There is no replacement Ext model.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory

/-- Paste the original comparison and index naturality into the full restriction square. -/
def restrictionNaturalitySquare
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : D ⥤ E) (J : D ⥤ C) (Q : E ⥤ C) (δ : J ⟶ F ⋙ Q)
    {A B : C} {s t : D} {v : E} (f : A ⟶ B) (g : B ⟶ Q.obj v)
    (j : A ⟶ J.obj s) (k : s ⟶ t) (e : v ⟶ F.obj s) (a : v ⟶ F.obj t)
    (he : e ≫ F.map k = a) (h : (f ≫ g) ≫ Q.map e = j ≫ δ.app s) :
    Square C where
  X₁ := A
  X₂ := B
  X₃ := J.obj s
  X₄ := Q.obj (F.obj t)
  f₁₂ := f
  f₂₄ := g ≫ Q.map a
  f₁₃ := j
  f₃₄ := J.map k ≫ δ.app t
  fac := by
    calc
      _ = (f ≫ g) ≫ Q.map a := (Category.assoc f g (Q.map a)).symm
      _ = ((f ≫ g) ≫ Q.map e) ≫ Q.map (F.map k) :=
        (congrArg (fun z => (f ≫ g) ≫ Q.map z) he.symm).trans
          ((congrArg (fun z => (f ≫ g) ≫ z) (Q.map_comp e (F.map k))).trans
            (Category.assoc (f ≫ g) (Q.map e) (Q.map (F.map k))).symm)
      _ = (j ≫ δ.app s) ≫ Q.map (F.map k) := congrArg (fun z => z ≫ Q.map (F.map k)) h
      _ = _ := (Category.assoc j (δ.app s) (Q.map (F.map k))).trans
        (congrArg (fun z => j ≫ z) (δ.naturality k).symm)

/-- Evaluate and paste the complete original indexed diagram only at the
variable-diagram layer, including its original transport and whole law family. -/
def indexedRestrictionSquare
    {I J D E C : Type*} [Category* I] [Category* J] [Category* D]
    [Category* E] [Category* C]
    (p : I ⥤ J) (a : J ⥤ E) (j : I ⥤ D) (b : D ⥤ E)
    (P : I ⥤ C) (B : J ⥤ C) (L : D ⥤ C) (Q : E ⥤ C)
    (gp : P ⟶ p ⋙ B) (ga : B ⟶ a ⋙ Q) (gj : P ⟶ j ⋙ L) (gb : L ⟶ b ⋙ Q)
    (τ : ∀ i, a.obj (p.obj i) ⟶ b.obj (j.obj i))
    (h : ∀ i, (gp.app i ≫ ga.app (p.obj i)) ≫ Q.map (τ i) =
      gj.app i ≫ gb.app (j.obj i))
    (i : I) {d : D} (κJ : j.obj i ⟶ d) (κA : a.obj (p.obj i) ⟶ b.obj d)
    (hk : τ i ≫ b.map κJ = κA) : Square C :=
  restrictionNaturalitySquare b L Q gb (gp.app i) (ga.app (p.obj i))
    (gj.app i) κJ (τ i) κA hk (h i)


namespace Functor

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ i₀ j₀ i₁ j₁ i₂ j₂ i₃ j₃ w

variable {C₀ : Type u₀} [Category.{v₀} C₀] [Abelian C₀] [HasExt.{w} C₀]
  {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasExt.{w} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasExt.{w} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasExt.{w} C₃]
  {I₀ : Type i₀} [Category.{j₀} I₀] {I₁ : Type i₁} [Category.{j₁} I₁]
  {I₂ : Type i₂} [Category.{j₂} I₂] {I₃ : Type i₃} [Category.{j₃} I₃]

/-- Construct all four original Ext diagrams and transfer families before
specialization, then evaluate the full indexed restriction square. The last
input is the original comparison family, not an additional native hypothesis. -/
def extDiagramRestrictionSquare
    (Lp : C₀ ⥤ C₁) [Lp.Additive] [PreservesFiniteLimits Lp] [PreservesFiniteColimits Lp]
    (La : C₁ ⥤ C₃) [La.Additive] [PreservesFiniteLimits La] [PreservesFiniteColimits La]
    (Lj : C₀ ⥤ C₂) [Lj.Additive] [PreservesFiniteLimits Lj] [PreservesFiniteColimits Lj]
    (Lb : C₂ ⥤ C₃) [Lb.Additive] [PreservesFiniteLimits Lb] [PreservesFiniteColimits Lb]
    (F₀ : I₀ ⥤ C₀) (F₁ : I₁ ⥤ C₁) (F₂ : I₂ ⥤ C₂) (F₃ : I₃ ⥤ C₃)
    (Hp : I₀ ⥤ I₁) (Ha : I₁ ⥤ I₃) (Hj : I₀ ⥤ I₂) (Hb : I₂ ⥤ I₃)
    (ep : F₀ ⋙ Lp ≅ Hp ⋙ F₁) (ea : F₁ ⋙ La ≅ Ha ⋙ F₃)
    (ej : F₀ ⋙ Lj ≅ Hj ⋙ F₂) (eb : F₂ ⋙ Lb ≅ Hb ⋙ F₃)
    {A₀ : C₀} {A₁ : C₁} {A₂ : C₂} {A₃ : C₃}
    (φp : Lp.obj A₀ ⟶ A₁) (φa : La.obj A₁ ⟶ A₃)
    (φj : Lj.obj A₀ ⟶ A₂) (φb : Lb.obj A₂ ⟶ A₃) (n : ℕ)
    (τ : ∀ i : I₀ᵒᵖ, Ha.op.obj (Hp.op.obj i) ⟶ Hb.op.obj (Hj.op.obj i))
    (i : I₀ᵒᵖ) {d : I₂ᵒᵖ} (κJ : Hj.op.obj i ⟶ d)
    (κA : Ha.op.obj (Hp.op.obj i) ⟶ Hb.op.obj d)
    (hk : τ i ≫ Hb.op.map κJ = κA) :
    let Q := (F₃.op ⋙ extFunctor n).flip.obj A₃
    let gp := Lp.extDiagramMap F₀ (Hp ⋙ F₁) ep φp n
    let ga := La.extDiagramMap F₁ (Ha ⋙ F₃) ea φa n
    let gj := Lj.extDiagramMap F₀ (Hj ⋙ F₂) ej φj n
    let gb := Lb.extDiagramMap F₂ (Hb ⋙ F₃) eb φb n
    (∀ v, (gp.app v ≫ ga.app (Hp.op.obj v)) ≫ Q.map (τ v) =
      gj.app v ≫ gb.app (Hj.op.obj v)) → Square AddCommGrpCat.{w} :=
  fun h => indexedRestrictionSquare Hp.op Ha.op Hj.op Hb.op
    ((F₀.op ⋙ extFunctor n).flip.obj A₀)
    ((F₁.op ⋙ extFunctor n).flip.obj A₁)
    ((F₂.op ⋙ extFunctor n).flip.obj A₂)
    ((F₃.op ⋙ extFunctor n).flip.obj A₃)
    (Lp.extDiagramMap F₀ (Hp ⋙ F₁) ep φp n)
    (La.extDiagramMap F₁ (Ha ⋙ F₃) ea φa n)
    (Lj.extDiagramMap F₀ (Hj ⋙ F₂) ej φj n)
    (Lb.extDiagramMap F₂ (Hb ⋙ F₃) eb φb n) τ h i κJ κA hk

end Functor

end CategoryTheory
