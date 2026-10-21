/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CofinalIdeals
public import Mathlib.RingTheory.LocalRing.Quotient

/-! # Extended maximal ideals in finite local algebras

The power bound is proved from the actual finite residue algebra and its
Artinianity, not assumed as a cofinality premise. No Noetherian hypothesis is
needed for this comparison.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace AdicCompletion

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable [IsLocalRing R] [IsLocalRing A]
variable [Module.Finite R A]

/-- The actual closed fibre of a finite local algebra is an Artinian residue algebra. -/
theorem finite_local_maximalIdeal_pow_le :
    ∃ N : ℕ, 0 < N ∧
      maximalIdeal A ^ N ≤ (maximalIdeal R).map (algebraMap R A) := by
  let J := (maximalIdeal R).map (algebraMap R A)
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have : Module.Finite (R ⧸ maximalIdeal R) (A ⧸ J) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinianRing (A ⧸ J) := IsArtinianRing.of_finite (R ⧸ maximalIdeal R) _
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient J
  exact ⟨N + 1, Nat.succ_pos _, (Ideal.pow_le_pow_right (Nat.le_succ N)).trans hN⟩

/-- A chosen exponent, accompanied by the theorem proving its actual ideal inequality. -/
def finiteLocalExponent : ℕ :=
  (finite_local_maximalIdeal_pow_le (R := R) (A := A)).choose

theorem finiteLocalExponent_pos : 0 < finiteLocalExponent (R := R) (A := A) :=
  (finite_local_maximalIdeal_pow_le (R := R) (A := A)).choose_spec.1

theorem pow_finiteLocalExponent_le :
    maximalIdeal A ^ finiteLocalExponent (R := R) (A := A) ≤
      (maximalIdeal R).map (algebraMap R A) :=
  (finite_local_maximalIdeal_pow_le (R := R) (A := A)).choose_spec.2

variable [IsLocalHom (algebraMap R A)]

/-- The native extended-maximal-ideal and maximal-ideal completions are equivalent. -/
def finiteLocalAlgEquiv :
    AdicCompletion ((maximalIdeal R).map (algebraMap R A)) A ≃ₐ[A]
      AdicCompletion (maximalIdeal A) A :=
  sandwichAlgEquiv _ _ (finiteLocalExponent (R := R) (A := A))
    finiteLocalExponent_pos (map_maximalIdeal_le (algebraMap R A))
    pow_finiteLocalExponent_le

@[simp] theorem evalₐ_finiteLocalAlgEquiv (c : ℕ)
    (x : AdicCompletion ((maximalIdeal R).map (algebraMap R A)) A) :
    evalₐ (maximalIdeal A) c (finiteLocalAlgEquiv (R := R) (A := A) x) =
      Ideal.Quotient.factor (pow_le_pow_left' (map_maximalIdeal_le (algebraMap R A)) c)
        (evalₐ ((maximalIdeal R).map (algebraMap R A)) c x) :=
  evalₐ_sandwichAlgEquiv _ _ _ _ _ _ c x

/-- The inverse comparison uses the actual proved cofinal exponent. -/
@[simp] theorem evalₐ_finiteLocalAlgEquiv_symm (c : ℕ)
    (x : AdicCompletion (maximalIdeal A) A) :
    evalₐ ((maximalIdeal R).map (algebraMap R A)) c
      ((finiteLocalAlgEquiv (R := R) (A := A)).symm x) =
      Ideal.Quotient.factor
        (show maximalIdeal A ^ (finiteLocalExponent (R := R) (A := A) * c) ≤
            ((maximalIdeal R).map (algebraMap R A)) ^ c by
          simpa only [pow_mul] using
            pow_le_pow_left' (pow_finiteLocalExponent_le (R := R) (A := A)) c)
        (evalₐ (maximalIdeal A) (finiteLocalExponent (R := R) (A := A) * c) x) :=
  evalₐ_sandwichAlgEquiv_symm _ _ _ _ _ _ c x

theorem finiteLocalAlgEquiv_algebraMap (a : A) :
    finiteLocalAlgEquiv (R := R) (A := A)
      (algebraMap A (AdicCompletion ((maximalIdeal R).map (algebraMap R A)) A) a) =
      algebraMap A (AdicCompletion (maximalIdeal A) A) a :=
  (finiteLocalAlgEquiv (R := R) (A := A)).commutes a

end AdicCompletion
