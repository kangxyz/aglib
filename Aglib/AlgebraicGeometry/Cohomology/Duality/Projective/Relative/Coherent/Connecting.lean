/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Ext
public import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# The original mapped Yoneda class and the target connecting map

A native connecting square carries the original Yoneda connecting class to
the target homology-sequence map. The target triangle retains its installed
third arrow, including any sign and shift comparisons already in that arrow.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Pretriangulated

universe u v w w' u' v'

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasExt.{w} C] [HasDerivedCategory.{w'} C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasShift D ℤ]

/-- Literal mapped Yoneda postcomposition satisfies the native target connecting square.
Only the supplied square is used; its original target arrow retains its native sign. -/
-- Retain the public Ext and additive-functor hypotheses used by the connecting-map callers.
@[nolint unusedArguments]
theorem map_homPlus_extClass_postcomp
    (F : DerivedCategory.Plus C ⥤ D) [F.Additive] [F.CommShift ℤ]
    {S : ShortComplex C} (hS : S.ShortExact) (T : Triangle D)
    (t₁ : F.obj ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁) ⟶ T.obj₁)
    (t₃ : F.obj ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₃) ⟶ T.obj₃)
    (h : ShiftedHom.map hS.singleTrianglePlus.mor₃ F ≫ t₁⟦(1 : ℤ)⟧' = t₃ ≫ T.mor₃)
    (M : C) (q : ℕ) (x : Ext.{w} M S.X₃ q) :
    ((x.comp hS.extClass rfl).homPlus.map F) ≫ t₁⟦((q + 1 : ℕ) : ℤ)⟧' =
      (preadditiveCoyoneda.obj
        (Opposite.op (F.obj ((DerivedCategory.Plus.singleFunctor C 0).obj M)))).homologySequenceδ
          T (q : ℤ) ((q + 1 : ℕ) : ℤ) (by omega)
          (x.homPlus.map F ≫ t₃⟦(q : ℤ)⟧') := by
  let α := x.homPlus.map F
  let δ := hS.extClass.homPlus.map F
  let τ₁ := ShiftedHom.mk₀ (0 : ℤ) rfl t₁
  let τ₃ := ShiftedHom.mk₀ (0 : ℤ) rfl t₃
  have ht : δ.comp τ₁ (zero_add (1 : ℤ)) = τ₃.comp T.mor₃ (add_zero (1 : ℤ)) := by
    rw [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp]
    change (hS.extClass.homPlus.map F) ≫ t₁⟦(1 : ℤ)⟧' = t₃ ≫ T.mor₃
    rw [Ext.homPlus_extClass]
    exact h
  have hcomp : ((x.comp hS.extClass rfl).homPlus.map F).comp τ₁ (zero_add _) =
      (preadditiveCoyoneda.obj
        (Opposite.op (F.obj ((DerivedCategory.Plus.singleFunctor C 0).obj M)))).homologySequenceδ
          T (q : ℤ) ((q + 1 : ℕ) : ℤ) (by omega) (α.comp τ₃ (zero_add _)) := by
    rw [preadditiveCoyoneda_homologySequenceδ_apply]
    change ((x.comp hS.extClass rfl).homPlus.map F).comp τ₁ _ =
      (α.comp τ₃ (zero_add _)).comp T.mor₃ (by omega)
    rw [Ext.homPlus_comp, ShiftedHom.map_comp]
    change (α.comp δ (by omega)).comp τ₁ (zero_add _) = _
    rw [ShiftedHom.comp_assoc α δ τ₁ (by omega) (zero_add _) (by omega), ht]
    exact (ShiftedHom.comp_assoc α τ₃ T.mor₃ (zero_add _) (add_zero _) (by omega)).symm
  simpa only [τ₁, τ₃, α, ShiftedHom.comp_mk₀] using hcomp

end CategoryTheory.Abelian.Ext
