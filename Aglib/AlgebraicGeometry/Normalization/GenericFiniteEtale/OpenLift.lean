/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.OpenRecovery

/-! # Restricting a genuine normalization lift to the original open cover

The original open-recovery square lifts a map on the complement. Its two
original projections are retained before any field or component is selected.
No normalization base-change comparison is used.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable {X U E : Scheme.{u}} [IsIntegral X] [Nonempty U]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  (j : U ⟶ X) [IsOpenImmersion j] (p : E ⟶ U) [IsFinite p] [Etale p]

/-- Restrict an actual normalization lift to the original complement.
The supplied equality is only its actual structural triangle. -/
theorem exists_openLift {Z W : Scheme.{u}}
    (a : Z ⟶ (genericMap j p).normalization) (k : W ⟶ Z) (v : W ⟶ U)
    (h : (k ≫ a) ≫ (genericMap j p).fromNormalization = v ≫ j) :
    ∃ b : W ⟶ E, b ≫ inclusion j p = k ≫ a ∧ b ≫ p = v := by
  exact ⟨(isPullback j p).lift (k ≫ a) v h,
    (isPullback j p).lift_fst _ _ _, (isPullback j p).lift_snd _ _ _⟩

/-- The original open lift has no implementation ambiguity. -/
theorem openLift_unique {W : Scheme.{u}} (a b : W ⟶ E)
    (h : a ≫ inclusion j p = b ≫ inclusion j p) : a = b :=
  (cancel_mono (inclusion j p)).mp h

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
