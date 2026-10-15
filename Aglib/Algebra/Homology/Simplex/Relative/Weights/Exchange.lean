/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Finite products of supported weight sums

For a finite row type `A` and any relation `P : A → W → Prop`, a family of
finitely supported sums of admissible weights is equivalent to a dependent
finitely supported sum over weights of functions on their admissible rows.
The equivalence is the native sigma-Finsupp/Pi comparison, an actual sigma
reindexing, and the native Finsupp/DFinsupp comparisons. Its component formula
retains each original coefficient.
-/

@[expose] public section

noncomputable section

namespace Finsupp

variable {A W : Type*}

/-- Swap the row and weight in the sigma type of related pairs. -/
def sigmaSubtypeSwapEquiv (P : A → W → Prop) :
    (Σ a : A, {w : W // P a w}) ≃ (Σ w : W, {a : A // P a w}) where
  toFun x := ⟨x.2.val, ⟨x.1, x.2.property⟩⟩
  invFun x := ⟨x.2.val, ⟨x.1, x.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (R : Type*) [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M] [Finite A]

/-- The actual finite product / dependent finitely supported weight-sum interchange. -/
def piSubtypeLEquivDFinsupp (P : A → W → Prop) :
    (∀ a : A, {w : W // P a w} →₀ M) ≃ₗ[R]
      (Π₀ w : W, ({a : A // P a w} → M)) := by
  classical
  letI := Fintype.ofFinite A
  exact (sigmaFinsuppLEquivPiFinsupp R).symm.trans
    ((Finsupp.domLCongr (sigmaSubtypeSwapEquiv P)).trans
      ((sigmaFinsuppLequivDFinsupp R).trans
        (DFinsupp.mapRange.linearEquiv fun w =>
          Finsupp.linearEquivFunOnFinite R M {a : A // P a w})))

/-- Every exchanged matrix entry is the original admissible weight coefficient. -/
@[simp]
theorem piSubtypeLEquivDFinsupp_apply (P : A → W → Prop)
    (x : ∀ a : A, {w : W // P a w} →₀ M) (w : W) (a : {a : A // P a w}) :
    piSubtypeLEquivDFinsupp (M := M) R P x w a = x a.val ⟨w, a.property⟩ := by
  classical
  simp [piSubtypeLEquivDFinsupp, sigmaSubtypeSwapEquiv, Finsupp.split_apply,
    Finsupp.equivMapDomain_apply]

/-- The inverse matrix entry has the same coefficient-preserving formula. -/
@[simp]
theorem piSubtypeLEquivDFinsupp_symm_apply (P : A → W → Prop)
    (x : Π₀ w : W, ({a : A // P a w} → M)) (a : A) (w : {w : W // P a w}) :
    (piSubtypeLEquivDFinsupp (M := M) R P).symm x a w = x w.val ⟨a, w.property⟩ := by
  have h := piSubtypeLEquivDFinsupp_apply R P
    ((piSubtypeLEquivDFinsupp (M := M) R P).symm x) w.val ⟨a, w.property⟩
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end Finsupp
