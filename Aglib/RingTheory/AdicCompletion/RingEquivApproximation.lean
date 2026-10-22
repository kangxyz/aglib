/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.RingEquiv
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # Transport of actual completion approximation across ring equivalences

All coefficients, formal roots, and finite quotient projections are transported
by their canonical maps. The exact solution is returned in the original ring,
with both literal quotient precision and original extended-ideal error.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace AdicCompletion

universe u v w z
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A solver for the actual mapped-ideal completion gives a solver in the original
ring, even when the rings live in different universes. No finite generation or
Noetherian assumption is needed for this transport. -/
theorem exists_solution_of_ringEquiv_solver
    (e : R ≃+* S) (I : Ideal R) {σ : Type w} {ι : Type z}
    (hsolve : ∀ (E : ι → MvPolynomial σ S)
      (t : σ → AdicCompletion (I.map (e : R →+* S)) S),
      (∀ i, eval₂ (algebraMap S (AdicCompletion (I.map (e : R →+* S)) S)) t (E i) = 0) →
      ∀ c : ℕ, ∃ b : σ → S,
        (∀ i, MvPolynomial.eval b (E i) = 0) ∧
        (∀ j, Ideal.Quotient.mk ((I.map (e : R →+* S)) ^ c) (b j) =
          evalₐ (I.map (e : R →+* S)) c (t j)) ∧
        ∀ j, algebraMap S (AdicCompletion (I.map (e : R →+* S)) S) (b j) - t j ∈
          ((I.map (e : R →+* S)) ^ c).map
            (algebraMap S (AdicCompletion (I.map (e : R →+* S)) S)))
    (F : ι → MvPolynomial σ R) (y : σ → AdicCompletion I R)
    (hy : ∀ i, eval₂ (algebraMap R (AdicCompletion I R)) y (F i) = 0) (c : ℕ) :
    ∃ x : σ → R,
      (∀ i, MvPolynomial.eval x (F i) = 0) ∧
      (∀ j, Ideal.Quotient.mk (I ^ c) (x j) = evalₐ I c (y j)) ∧
      ∀ j, algebraMap R (AdicCompletion I R) (x j) - y j ∈
        (I ^ c).map (algebraMap R (AdicCompletion I R)) := by
  let E : ι → MvPolynomial σ S := fun i => MvPolynomial.map (e : R →+* S) (F i)
  let t : σ → AdicCompletion (I.map (e : R →+* S)) S := fun j => congrRingEquiv e I (y j)
  have ht (i : ι) : eval₂
      (algebraMap S (AdicCompletion (I.map (e : R →+* S)) S)) t (E i) = 0 := by
    have h := congrArg (congrRingEquiv e I).toRingHom (hy i)
    rw [hom_eval₂, map_zero] at h
    have hc : (congrRingEquiv e I).toRingHom.comp
        (algebraMap R (AdicCompletion I R)) =
          (algebraMap S (AdicCompletion (I.map (e : R →+* S)) S)).comp (e : R →+* S) :=
      RingHom.ext fun r => congrRingEquiv_algebraMap e I r
    rw [hc] at h
    have htfun : (fun j => (congrRingEquiv e I).toRingHom (y j)) = t := by
      funext j
      rfl
    rw [htfun] at h
    change eval₂ _ t (MvPolynomial.map (e : R →+* S) (F i)) = 0
    rw [eval₂_map]
    exact h
  obtain ⟨b, hb, hprec, herr⟩ := hsolve E t ht c
  let x : σ → R := fun j => e.symm (b j)
  refine ⟨x, ?_, ?_, ?_⟩
  · intro i
    apply e.injective
    change (e : R →+* S) (MvPolynomial.eval x (F i)) = (e : R →+* S) 0
    rw [MvPolynomial.eval₂_comp, map_zero]
    have h := hb i
    simp only [E, eval_map] at h
    simpa only [x, Function.comp_def, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] using h
  · intro j
    apply (quotientPowEquiv e I c).injective
    rw [quotientPowEquiv_mk]
    change Ideal.Quotient.mk ((I.map (e : R →+* S)) ^ c) (e (e.symm (b j))) = _
    rw [e.apply_symm_apply]
    exact (hprec j).trans (evalₐ_congrRingEquiv e I c (y j))
  · intro j
    have h := herr j
    rw [← congrRingEquiv_map_power e I c] at h
    obtain ⟨a, ha, he⟩ :=
      (Ideal.mem_map_iff_of_surjective (congrRingEquiv e I).toRingHom
        (congrRingEquiv e I).surjective).mp h
    have he' : congrRingEquiv e I a = congrRingEquiv e I
        (algebraMap R (AdicCompletion I R) (x j) - y j) := by
      rw [map_sub, congrRingEquiv_algebraMap]
      change congrRingEquiv e I a =
        algebraMap S (AdicCompletion (I.map (e : R →+* S)) S) (b j) - t j at he
      simpa only [x, t, RingEquiv.apply_symm_apply] using he
    exact (congrRingEquiv e I).injective he' ▸ ha

end AdicCompletion
