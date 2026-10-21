/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Compatible lifts in a surjective natural-number tower

Every element of every stage lifts to a native section when all adjacent
transition maps are surjective. The construction uses dependent choice on the
tail starting at the prescribed stage, then the original transition maps.
There is no finiteness, topology or algebra hypothesis.
-/

@[expose] public noncomputable section

open Opposite

universe u

namespace CategoryTheory.Functor

variable (F : ℕᵒᵖ ⥤ Type u)

/-- Compatibility along adjacent arrows implies compatibility along every
arrow of the original natural-number tower. -/
theorem mem_sections_of_succ (s : ∀ n : ℕ, F.obj (op n))
    (hs : ∀ n, F.map (homOfLE (Nat.le_succ n)).op (s (n + 1)) = s n) :
    (fun j : ℕᵒᵖ => s j.unop) ∈ F.sections := by
  intro j k f
  have h : k.unop ≤ j.unop := leOfHom f.unop
  have H : ∀ a b (h : a ≤ b), F.map (homOfLE h).op (s b) = s a := by
    intro a b h
    induction h with
    | refl => simp
    | @step b h ih =>
      have he : (homOfLE (Nat.le.step h)).op =
          (homOfLE (Nat.le_succ b)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
      rw [he, F.map_comp]
      change F.map (homOfLE h).op
        (F.map (homOfLE (Nat.le_succ b)).op (s (b + 1))) = s a
      rw [hs, ih]
  have hf : f = (homOfLE h).op := Subsingleton.elim _ _
  rw [hf]
  exact H _ _ h

/-- Every original evaluation map from native sections is surjective if
all adjacent original transition maps are surjective. -/
theorem sections_eval_surjective_of_surjective_succ
    (h : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op))
    (n : ℕ) : Function.Surjective (fun s : F.sections => s.val (op n)) := by
  intro x
  let s : ∀ k : ℕ, F.obj (op (n + k)) :=
    fun k => Nat.rec x (fun k y => (h (n + k) y).choose) k
  have hs (k : ℕ) :
      F.map (homOfLE (Nat.le_succ (n + k))).op (s (k + 1)) = s k :=
    (h (n + k) (s k)).choose_spec
  have hc : ∀ a b (hab : a ≤ b),
      F.map (homOfLE (Nat.add_le_add_left hab n)).op (s b) = s a := by
    intro a b hab
    induction hab with
    | refl => simp
    | @step b hab ih =>
      have he : (homOfLE (Nat.add_le_add_left (Nat.le.step hab) n)).op =
          (homOfLE (Nat.le_succ (n + b))).op ≫
            (homOfLE (Nat.add_le_add_left hab n)).op := Subsingleton.elim _ _
      rw [he, F.map_comp]
      change F.map (homOfLE (Nat.add_le_add_left hab n)).op
        (F.map (homOfLE (Nat.le_succ (n + b))).op (s (b + 1))) = s a
      rw [hs, ih]
  let t (k : ℕ) : F.obj (op k) :=
    F.map (homOfLE (Nat.le_add_left k n)).op (s k)
  have ht (k : ℕ) : F.map (homOfLE (Nat.le_succ k)).op (t (k + 1)) = t k := by
    change F.map (homOfLE (Nat.le_succ k)).op
      (F.map (homOfLE (Nat.le_add_left (k + 1) n)).op (s (k + 1))) =
        F.map (homOfLE (Nat.le_add_left k n)).op (s k)
    have he : (homOfLE (Nat.le_add_left (k + 1) n)).op ≫
          (homOfLE (Nat.le_succ k)).op =
        (homOfLE (Nat.le_succ (n + k))).op ≫
          (homOfLE (Nat.le_add_left k n)).op := Subsingleton.elim _ _
    have hm := congrArg (fun g => F.map g (s (k + 1))) he
    simpa only [F.map_comp, types_comp_apply, hs] using hm
  refine ⟨⟨fun j => t j.unop, F.mem_sections_of_succ t ht⟩, ?_⟩
  exact hc 0 n (Nat.zero_le n)

end CategoryTheory.Functor
