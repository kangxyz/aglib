/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.MvPolynomial.Funext

/-! # Rational points in nonempty opens of affine space -/

@[expose] public section

namespace AlgebraicGeometry.Scheme

universe u v

/-- Over an infinite field, every nonempty open of polynomial affine space
contains an evaluation point over the original field. -/
theorem exists_eval_mem_open (K : Type (max u v)) [Field K] [Infinite K]
    (σ : Type v) (U : (Spec (.of (MvPolynomial σ K))).Opens)
    (hU : (U : Set (Spec (.of (MvPolynomial σ K)))).Nonempty) :
    ∃ a : σ → K,
      (Spec.map (CommRingCat.ofHom (MvPolynomial.eval a))) default ∈ U := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨_, ⟨p, rfl⟩, hxp, hpU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp U.isOpen x hx
  have hp : p ≠ 0 := by
    intro h
    apply (show p ∉ x.asIdeal from hxp)
    rw [h]
    exact x.asIdeal.zero_mem
  obtain ⟨a, ha⟩ : ∃ a : σ → K, MvPolynomial.eval a p ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    apply MvPolynomial.funext
    simpa using h
  refine ⟨a, hpU ?_⟩
  change MvPolynomial.eval a p ∉ (default : Spec (.of K)).asIdeal
  simpa only [default_asIdeal, Ideal.mem_bot] using ha

end AlgebraicGeometry.Scheme
