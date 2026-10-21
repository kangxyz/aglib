/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationNativeCompletion
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationApproximation

/-! # Artin approximation in the actual native completion

This endpoint uses the original completion algebra map, original finite
quotient projections, and actual extended ideal powers. Its proof transports
through the genuine completion equivalence, never a caller-supplied isomorphism.
The source is the polynomial-local henselization over an arbitrary field.
-/

@[expose] public section
noncomputable section

open IsLocalRing MvPolynomial

namespace PolynomialLocalHenselization

universe u
variable (k : Type u) [Field k] (n : ℕ)

local notation "H" => PolynomialLocalHenselization k n
local notation "Hhat" => AdicCompletion (maximalIdeal H) H

/-- Every native completed root admits an exact henselized root with identical
original quotient projection at any prescribed order. No separability,
approximation, or completion-isomorphism oracle is a hypothesis. -/
theorem exists_solution_native_completion
    {σ ι : Type*} [Finite σ] [Finite ι]
    (F : ι → MvPolynomial σ H) (y : σ → Hhat)
    (hy : ∀ i, eval₂ (algebraMap H Hhat) y (F i) = 0) (c : ℕ) :
    ∃ x : σ → H,
      (∀ i, eval x (F i) = 0) ∧
      ∀ j, Ideal.Quotient.mk (maximalIdeal H ^ c) (x j) =
        AdicCompletion.evalₐ (maximalIdeal H) c (y j) := by
  let e := completionFormalEquiv k n
  have he : e.toRingHom.comp (algebraMap H Hhat) = (toFormalSeries k n).toRingHom := by
    apply RingHom.ext
    intro a
    exact completionFormalEquiv_algebraMap k n a
  have hy' : ∀ i, eval₂ (toFormalSeries k n).toRingHom
      (fun j => e (y j)) (F i) = 0 := by
    intro i
    have h := congrArg e.toRingHom (hy i)
    rw [MvPolynomial.hom_eval₂, he, map_zero] at h
    exact h
  obtain ⟨x, hx, hprec⟩ := exists_solution_approximation k n F (fun j => e (y j)) hy' c
  refine ⟨x, hx, fun j => ?_⟩
  have hq : AdicCompletion.evalₐ (maximalIdeal H) c (algebraMap H Hhat (x j)) =
      AdicCompletion.evalₐ (maximalIdeal H) c (y j) := by
    apply (completionFormalEquiv_sub_mem_iff k n c _ _).mp
    simpa only [completionFormalEquiv_algebraMap] using hprec j
  change AdicCompletion.evalₐ (maximalIdeal H) c
    (AdicCompletion.of (maximalIdeal H) H (x j)) = _ at hq
  rwa [AdicCompletion.evalₐ_of] at hq

/-- The same exact root has both native quotient equality and an error in the
extension of the actual source maximal-ideal power. This includes order zero. -/
theorem exists_solution_native_completion_with_precision
    {σ ι : Type*} [Finite σ] [Finite ι]
    (F : ι → MvPolynomial σ H) (y : σ → Hhat)
    (hy : ∀ i, eval₂ (algebraMap H Hhat) y (F i) = 0) (c : ℕ) :
    ∃ x : σ → H,
      (∀ i, eval x (F i) = 0) ∧
      (∀ j, Ideal.Quotient.mk (maximalIdeal H ^ c) (x j) =
        AdicCompletion.evalₐ (maximalIdeal H) c (y j)) ∧
      ∀ j, algebraMap H Hhat (x j) - y j ∈
        (maximalIdeal H ^ c).map (algebraMap H Hhat) := by
  obtain ⟨x, hx, hq⟩ := exists_solution_native_completion k n F y hy c
  refine ⟨x, hx, hq, fun j => ?_⟩
  apply (native_eval_eq_iff_sub_mem k n c _ _).mp
  change AdicCompletion.evalₐ (maximalIdeal H) c
    (AdicCompletion.of (maximalIdeal H) H (x j)) = _
  rw [AdicCompletion.evalₐ_of]
  exact hq j

end PolynomialLocalHenselization
