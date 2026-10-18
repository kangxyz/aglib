/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Cofinal powers in adic completions

The completion is unchanged on replacing an ideal by a positive power. All comparison maps
are constructed from the actual quotient projections.
-/

@[expose] public section
noncomputable section

namespace AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- Compatibility of the ring-valued projections with the quotient transition maps. -/
theorem factor_evalₐ {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (evalₐ I n x) = evalₐ I m x := by
  simp only [evalₐ, AlgHom.coe_comp, Function.comp_apply,
    Ideal.quotientEquivAlgOfEq_coe_eq_factorₐ]
  change Ideal.Quotient.factor (Ideal.pow_le_pow_right h)
      (Ideal.Quotient.factor (by simp) (x.val n)) =
    Ideal.Quotient.factor (by simp) (x.val m)
  rw [← x.prop h]
  change Ideal.Quotient.factor (Ideal.pow_le_pow_right h)
      (Ideal.Quotient.factor (by simp) (x.val n)) =
    Ideal.Quotient.factor (by simp)
      (Ideal.Quotient.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right h)) (x.val n))
  simp only [Ideal.Quotient.factor_comp_apply]

/-- A cofinal comparison of ideal-power filtrations induces an actual algebra map. -/
def reindexAlgHom (J : Ideal R) (a : ℕ → ℕ) (ha : Monotone a)
    (h : ∀ n, I ^ a n ≤ J ^ n) : AdicCompletion I R →ₐ[R] AdicCompletion J R :=
  liftAlgHom J (fun n ↦ (Ideal.Quotient.factorₐ R (h n)).comp (evalₐ I (a n)))
    (fun {m n} hmn ↦ by
      ext x
      change Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
          (Ideal.Quotient.factor (h n) (evalₐ I (a n) x)) =
        Ideal.Quotient.factor (h m) (evalₐ I (a m) x)
      rw [← factor_evalₐ I (ha hmn) x]
      simp only [Ideal.Quotient.factor_comp_apply])

@[simp] theorem evalₐ_reindexAlgHom (J : Ideal R) (a : ℕ → ℕ) (ha : Monotone a)
    (h : ∀ n, I ^ a n ≤ J ^ n) (n : ℕ) (x : AdicCompletion I R) :
    evalₐ J n (reindexAlgHom I J a ha h x) =
      Ideal.Quotient.factor (h n) (evalₐ I (a n) x) := by
  simp [reindexAlgHom]

set_option backward.isDefEq.respectTransparency false in
/-- A positive power gives the same actual adic completion as an algebra. -/
def powAlgEquiv (e : ℕ) (he : 0 < e) :
    AdicCompletion (I ^ e) R ≃ₐ[R] AdicCompletion I R := by
  let f := reindexAlgHom (I ^ e) I id monotone_id
    (fun n ↦ by simpa only [pow_mul, id_eq] using
      (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n he) : I ^ (e * n) ≤ I ^ n))
  let g := reindexAlgHom I (I ^ e) (fun n ↦ e * n)
    (fun ⦃_ _⦄ h ↦ Nat.mul_le_mul_left e h) (fun n ↦ le_of_eq (pow_mul I e n))
  refine { f with invFun := g, left_inv := ?_, right_inv := ?_ }
  · intro x
    apply ext_evalₐ
    intro n
    change evalₐ (I ^ e) n (g (f x)) = _
    simp only [g, f, evalₐ_reindexAlgHom, id_eq]
    rw [Ideal.Quotient.factor_comp_apply]
    exact factor_evalₐ (I ^ e) (Nat.le_mul_of_pos_left n he) x
  · intro x
    apply ext_evalₐ
    intro n
    change evalₐ I n (f (g x)) = _
    simp only [g, f, evalₐ_reindexAlgHom, id_eq]
    rw [Ideal.Quotient.factor_comp_apply]
    exact factor_evalₐ I (Nat.le_mul_of_pos_left n he) x

theorem powAlgEquiv_algebraMap (e : ℕ) (he : 0 < e) (r : R) :
    powAlgEquiv I e he (algebraMap R (AdicCompletion (I ^ e) R) r) =
      algebraMap R (AdicCompletion I R) r :=
  (powAlgEquiv I e he).commutes r

end AdicCompletion
