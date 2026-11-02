/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.Coefficients
public import Mathlib.CategoryTheory.Square

/-! # Complete coefficient squares of the original Ext diagram transfer

All four original diagram objects, coefficient edges and exact-transfer edges
are constructed together over variable abelian categories. The commuting law
is the existing law of that same Ext transfer. Geometric specialization only
supplies its original free-object diagrams and exact inverse-image functor.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Functor

universe i j k l u v u' v' w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w} D]
  {I : Type i} [Category.{j} I] {J : Type k} [Category.{l} J]

/-- The complete square of the original exact Ext-diagram transformation,
including both coefficient edges, both transfer edges and the original law. -/
def extDiagramCoefficientSquare
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (F : I ⥤ C) (G : J ⥤ D) (H : I ⥤ J) (e : F ⋙ L ≅ H ⋙ G)
    {A A' : C} {B B' : D} (a : L.obj A ⟶ B) (a' : L.obj A' ⟶ B')
    (f : A ⟶ A') (g : B ⟶ B') (h : L.map f ≫ a' = a ≫ g) (n : ℕ) :
    Square (Iᵒᵖ ⥤ AddCommGrpCat.{w}) where
  X₁ := (F.op ⋙ extFunctor n).flip.obj A
  X₂ := (F.op ⋙ extFunctor n).flip.obj A'
  X₃ := H.op ⋙ (G.op ⋙ extFunctor n).flip.obj B
  X₄ := H.op ⋙ (G.op ⋙ extFunctor n).flip.obj B'
  f₁₂ := (F.op ⋙ extFunctor n).flip.map f
  f₁₃ := L.extDiagramMap F (H ⋙ G) e a n
  f₂₄ := L.extDiagramMap F (H ⋙ G) e a' n
  f₃₄ := whiskerLeft H.op ((G.op ⋙ extFunctor n).flip.map g)
  fac := L.extDiagramMap_coefficients F G H e a a' f g h n

end CategoryTheory.Functor
