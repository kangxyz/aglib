/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Correcting primitives compatibly with a surjective chain map

This is the local algebraic correction in Stacks 0AAT. It is independent of
ordinal recursion. At an ordinal stage the target must be the limit of all
predecessors, not merely one selected earlier stage.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace CochainComplex

variable {X Y : CochainComplex AddCommGrpCat.{u} ℤ}

/-- Exactness at one degree supplies an actual primitive of an actual cycle. -/
lemma exists_primitive_of_exactAt (n : ℤ) (hX : X.ExactAt n)
    (x : X.X n) (hx : X.d n (n + 1) x = 0) :
    ∃ z : X.X (n - 1), X.d (n - 1) n z = x := by
  rw [X.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)] at hX
  exact ((X.sc' (n - 1) n (n + 1)).ab_exact_iff.mp hX) x hx

/-- A primitive can be corrected to match a prescribed primitive downstairs.
Only surjectivity two degrees below the cycle is required. -/
lemma exists_compatible_primitive (p : X ⟶ Y) (n : ℤ)
    (hX : X.ExactAt n) (hY : Y.ExactAt (n - 1))
    (hp : Function.Surjective (p.f (n - 2)))
    (x : X.X n) (hx : X.d n (n + 1) x = 0)
    (y : Y.X (n - 1)) (hy : Y.d (n - 1) n y = p.f n x) :
    ∃ z : X.X (n - 1), X.d (n - 1) n z = x ∧ p.f (n - 1) z = y := by
  obtain ⟨z₀, hz₀⟩ := exists_primitive_of_exactAt n hX x hx
  have hc : Y.d (n - 1) n (y - p.f (n - 1) z₀) = 0 := by
    have hcomm := congrArg (fun a => a z₀) (p.comm (n - 1) n)
    simp only [ConcreteCategory.comp_apply] at hcomm
    rw [map_sub, hy, hcomm, hz₀, sub_self]
  rw [Y.exactAt_iff' (n - 2) (n - 1) n (by simp; omega) (by simp)] at hY
  obtain ⟨t, ht⟩ := ((Y.sc' (n - 2) (n - 1) n).ab_exact_iff.mp hY)
    (y - p.f (n - 1) z₀) hc
  change Y.d (n - 2) (n - 1) t = y - p.f (n - 1) z₀ at ht
  obtain ⟨s, hs⟩ := hp t
  refine ⟨z₀ + X.d (n - 2) (n - 1) s, ?_, ?_⟩
  · have hdd := congrArg (fun a => a s) (X.d_comp_d (n - 2) (n - 1) n)
    simp only [ConcreteCategory.comp_apply] at hdd
    simp [map_add, hz₀, hdd]
  · have hcomm := congrArg (fun a => a s) (p.comm (n - 2) (n - 1))
    simp only [ConcreteCategory.comp_apply] at hcomm
    rw [map_add, ← hcomm, hs, ht]
    abel

end CochainComplex
