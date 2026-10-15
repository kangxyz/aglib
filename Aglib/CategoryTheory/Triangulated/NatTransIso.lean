/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor
/-! # Isomorphism propagation for actual shift-compatible natural transformations -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
universe v u v' u'
namespace CategoryTheory.NatTrans
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated] (τ : F ⟶ G) [τ.CommShift ℤ]

/-- The actual three components of a shift-compatible natural transformation form a triangle map. -/
def mapTriangleHom (T : Triangle C) : F.mapTriangle.obj T ⟶ G.mapTriangle.obj T where
  hom₁ := τ.app T.obj₁
  hom₂ := τ.app T.obj₂
  hom₃ := τ.app T.obj₃
  comm₁ := τ.naturality T.mor₁
  comm₂ := τ.naturality T.mor₂
  comm₃ := by
    dsimp
    simp only [Category.assoc, NatTrans.shift_app_comm τ (1 : ℤ) T.obj₁,
      NatTrans.naturality_assoc]

/-- Isomorphisms at the two ends of a distinguished triangle force the middle original component
  to be invertible. -/
theorem isIso_app_middle_of_distinguished (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsIso (τ.app T.obj₁)) (h₃ : IsIso (τ.app T.obj₃)) : IsIso (τ.app T.obj₂) :=
  isIso₂_of_isIso₁₃ (mapTriangleHom τ T) (F.map_distinguished _ hT)
    (G.map_distinguished _ hT) h₁ h₃

end CategoryTheory.NatTrans
