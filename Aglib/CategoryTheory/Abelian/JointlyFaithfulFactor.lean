/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-! # Original factors detected by a jointly faithful family

The actual zero-preserving functors detect that the original arrow kills the
cokernel of the original mono. Native Abelian.monoLift constructs a factor
through that same mono. No exactness of the detecting functors is required.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Abelian

universe uC vC uJ uD vD

/-- Local lifts through the pullbacks of one fixed original mono give an
actual lift through that original mono. Exactness of the detecting functors
is not required. -/
theorem exists_factor_of_jointlyFaithful
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {J : Type uJ} {D : J → Type uD} [∀ j, Category.{vD} (D j)]
    (L : ∀ j, C ⥤ D j) [∀ j, HasZeroMorphisms (D j)]
    [∀ j, (L j).PreservesZeroMorphisms] (hL : JointlyFaithful L)
    {A B F : C} (τ : A ⟶ B) [Mono τ] (α : F ⟶ B)
    (hlocal : ∀ j, ∃ β : (L j).obj F ⟶ (L j).obj A,
      β ≫ (L j).map τ = (L j).map α) :
    ∃ β : F ⟶ A, β ≫ τ = α := by
  have hz : α ≫ cokernel.π τ = 0 := by
    apply hL.map_injective
    intro j
    obtain ⟨β, hβ⟩ := hlocal j
    rw [(L j).map_comp, (L j).map_zero, ← hβ, Category.assoc,
      ← (L j).map_comp, cokernel.condition, (L j).map_zero, comp_zero]
  exact ⟨Abelian.monoLift τ α hz, Abelian.monoLift_comp τ α hz⟩


end CategoryTheory.Abelian
