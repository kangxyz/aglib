/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.CommSq

/-! # The original cohomology comparison commutes with base change

The vertical maps in this square are the original cohomology pullbacks. The
statement is a commuting square, not an invertibility assertion for these maps.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory

universe v

/-- A functor sends a commuting square with specified input transports to a commuting
square on elements. All actual objects and maps stay opaque in the proof. -/
theorem functor_map_square_element {C : Type*} [Category* C]
    (H : C ⥤ AddCommGrpCat.{v}) {A B C₀ D : C}
    (e₁ : A ⟶ B) (t : A ⟶ C₀) (e₂ : C₀ ⟶ D) (δ : B ⟶ D)
    (hsquare : e₁ ≫ δ = t ≫ e₂)
    (a : H.obj A) (b : H.obj B) (c : H.obj C₀) (d : H.obj D)
    (h₁ : H.map e₁ a = b) (ht : H.map t a = c) (h₂ : H.map e₂ c = d) :
    H.map δ b = d := by
  have h := ConcreteCategory.congr_hom ((CommSq.mk hsquare).map H).w a
  simp only [AddCommGrpCat.comp_apply] at h
  exact (congrArg (H.map δ) h₁.symm).trans
    (h.trans ((congrArg (H.map e₂) ht).trans h₂))

end CategoryTheory
