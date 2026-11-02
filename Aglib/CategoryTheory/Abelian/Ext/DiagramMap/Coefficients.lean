/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap

/-! # Coefficient squares for the original Ext diagram transformation

The complete natural-transformation equation retains the original target
index functor and whiskering, before any geometric diagrams are supplied.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Functor

universe i j k l u v u' v' w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w} D]
  {I : Type i} [Category.{j} I] {J : Type k} [Category.{l} J]

/-- An actual coefficient square gives the whole original diagram-map square,
including the literal target reindexing. No geometric specialization is used. -/
theorem extDiagramMap_coefficients
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (F : I ⥤ C) (G : J ⥤ D) (H : I ⥤ J) (e : F ⋙ L ≅ H ⋙ G)
    {A A' : C} {B B' : D} (a : L.obj A ⟶ B) (a' : L.obj A' ⟶ B')
    (f : A ⟶ A') (g : B ⟶ B') (h : L.map f ≫ a' = a ≫ g) (n : ℕ) :
    (F.op ⋙ extFunctor n).flip.map f ≫ L.extDiagramMap F (H ⋙ G) e a' n =
      L.extDiagramMap F (H ⋙ G) e a n ≫
        whiskerLeft H.op ((G.op ⋙ extFunctor n).flip.map g) := by
  ext U x
  exact (DFunLike.congr_fun
    (L.extCoefficientTransfer_naturality (e.inv.app U.unop) a a' f g h n) x).symm

end CategoryTheory.Functor
