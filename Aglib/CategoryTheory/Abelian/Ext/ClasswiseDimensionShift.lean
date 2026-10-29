/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.Exact

/-! # Classwise dimension shifting for Ext

Suppose degree-two Ext from a fixed source vanishes on a coefficient class.
If every higher individual class can be killed by a monomorphism whose literal
cokernel remains in that class, the native Ext exact sequence reduces it to
one lower degree. The middle object need not belong to the coefficient class
or be injective or acyclic.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Classwise monomorphic effacement with coefficient-class cokernels reduces
every degree at least two to degree two. The effacement witness is allowed to
depend on the individual class. -/
theorem eq_zero_of_classwise_effaceable (S : C) (P : C → Prop)
    (h₂ : ∀ (A : C), P A → Subsingleton (Ext.{w} S A 2))
    (heff : ∀ (A : C), P A → ∀ (n : ℕ) (α : Ext.{w} S A (n + 2 + 1)),
      ∃ (B : C) (i : A ⟶ B), Mono i ∧ P (cokernel i) ∧
        α.comp (mk₀ i) (Nat.add_zero (n + 2 + 1)) = 0)
    {A : C} (hA : P A) (n : ℕ) (α : Ext.{w} S A (n + 2)) : α = 0 := by
  induction n generalizing A with
  | zero => exact (h₂ A hA).elim _ _
  | succ n ih =>
    obtain ⟨B, i, hi, hQ, hα⟩ := heff A hA n α
    let : Mono i := hi
    let T := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel i }
    obtain ⟨β, hβ⟩ := covariant_sequence_exact₁ S hT α hα rfl
    rw [← hβ, ih hQ β, zero_comp]

end CategoryTheory.Abelian.Ext
