/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Congruence in adic completions

For a finitely generated ideal, equality under the canonical finite-order projection is
membership of the difference in the extended ideal power. This also identifies equality of
quotient-valued algebra maps with pointwise approximation in the original completion.
-/

@[expose] public section

namespace AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The kernel of the canonical projection is the extended ideal power. -/
theorem ker_evalₐ_eq_map (hI : I.FG) (n : ℕ) :
    RingHom.ker (evalₐ I n).toRingHom =
      (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  ext x
  trans x ∈ (eval I R n).ker
  · have h : (I ^ n • (⊤ : Ideal R)) = I ^ n := by simp
    change (Ideal.quotientEquivAlgOfEq R h) (eval I R n x) = 0 ↔
      eval I R n x = 0
    exact map_eq_zero_iff _ (AlgEquiv.injective _)
  · simp [← pow_smul_top_eq_ker_eval hI]

/-- Two completion elements have the same canonical projection exactly when their difference
belongs to the extension of the corresponding ideal power. This includes order zero. -/
theorem evalₐ_eq_iff_sub_mem (hI : I.FG) (n : ℕ) (x y : AdicCompletion I R) :
    evalₐ I n x = evalₐ I n y ↔
      x - y ∈ (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  rw [← ker_evalₐ_eq_map I hI n]
  change evalₐ I n x = evalₐ I n y ↔ evalₐ I n (x - y) = 0
  rw [map_sub, sub_eq_zero]

/-- Exact equality of the canonical quotient-valued algebra maps is equivalent to the
pointwise ideal-adic error criterion, with the errors measured in the actual completion. -/
theorem mkₐ_comp_eq_evalₐ_comp_iff {D : Type*} [CommRing D] [Algebra R D]
    (hI : I.FG) (n : ℕ) (f : D →ₐ[R] AdicCompletion I R) (g : D →ₐ[R] R) :
    (Ideal.Quotient.mkₐ R (I ^ n)).comp g = (evalₐ I n).comp f ↔
      ∀ d, f d - algebraMap R (AdicCompletion I R) (g d) ∈
        (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  constructor
  · intro h d
    apply (evalₐ_eq_iff_sub_mem I hI n _ _).mp
    rw [(evalₐ I n).commutes]
    exact (AlgHom.congr_fun h d).symm
  · intro h
    ext d
    have hd := (evalₐ_eq_iff_sub_mem I hI n _ _).mpr (h d)
    rw [(evalₐ I n).commutes] at hd
    exact hd.symm

end AdicCompletion
