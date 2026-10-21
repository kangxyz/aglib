/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.Powers

/-! # Actual completion equivalences for cofinal ideal powers -/

@[expose] public noncomputable section

namespace AdicCompletion

variable {R : Type*} [CommRing R] (I J : Ideal R)

/-- An actual ideal-power sandwich gives an equivalence of the native completions. -/
def sandwichAlgEquiv (N : ℕ) (hN : 0 < N) (hJI : J ≤ I) (hIJ : I ^ N ≤ J) :
    AdicCompletion J R ≃ₐ[R] AdicCompletion I R := by
  let f := reindexAlgHom J I id monotone_id (fun c ↦ pow_le_pow_left' hJI c)
  have hm : Monotone (fun c : ℕ ↦ N * c) := fun ⦃_ _⦄ h ↦ Nat.mul_le_mul_left N h
  let g := reindexAlgHom I J (fun c ↦ N * c) hm
    (fun c ↦ by simpa only [pow_mul] using pow_le_pow_left' hIJ c)
  refine { f with invFun := g, left_inv := ?_, right_inv := ?_ }
  · intro x
    apply ext_evalₐ
    intro c
    change evalₐ J c (g (f x)) = _
    simp only [g, f, evalₐ_reindexAlgHom, id_eq]
    rw [Ideal.Quotient.factor_comp_apply]
    exact factor_evalₐ J (Nat.le_mul_of_pos_left c hN) x
  · intro x
    apply ext_evalₐ
    intro c
    change evalₐ I c (f (g x)) = _
    simp only [g, f, evalₐ_reindexAlgHom, id_eq]
    rw [Ideal.Quotient.factor_comp_apply]
    exact factor_evalₐ I (Nat.le_mul_of_pos_left c hN) x

@[simp] theorem evalₐ_sandwichAlgEquiv (N : ℕ) (hN : 0 < N)
    (hJI : J ≤ I) (hIJ : I ^ N ≤ J) (c : ℕ) (x : AdicCompletion J R) :
    evalₐ I c (sandwichAlgEquiv I J N hN hJI hIJ x) =
      Ideal.Quotient.factor (pow_le_pow_left' hJI c) (evalₐ J c x) := by
  exact evalₐ_reindexAlgHom J I id monotone_id (fun c ↦ pow_le_pow_left' hJI c) c x

@[simp] theorem evalₐ_sandwichAlgEquiv_symm (N : ℕ) (hN : 0 < N)
    (hJI : J ≤ I) (hIJ : I ^ N ≤ J) (c : ℕ) (x : AdicCompletion I R) :
    evalₐ J c ((sandwichAlgEquiv I J N hN hJI hIJ).symm x) =
      Ideal.Quotient.factor
        (show I ^ (N * c) ≤ J ^ c by
          simpa only [pow_mul] using pow_le_pow_left' hIJ c)
        (evalₐ I (N * c) x) := by
  exact evalₐ_reindexAlgHom I J (fun c ↦ N * c)
    (fun ⦃_ _⦄ h ↦ Nat.mul_le_mul_left N h)
    (fun c ↦ by simpa only [pow_mul] using pow_le_pow_left' hIJ c) c x

theorem sandwichAlgEquiv_algebraMap (N : ℕ) (hN : 0 < N)
    (hJI : J ≤ I) (hIJ : I ^ N ≤ J) (r : R) :
    sandwichAlgEquiv I J N hN hJI hIJ (algebraMap R (AdicCompletion J R) r) =
      algebraMap R (AdicCompletion I R) r :=
  (sandwichAlgEquiv I J N hN hJI hIJ).commutes r

end AdicCompletion
