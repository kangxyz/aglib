/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationDVRApproximation
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationNativeCompletion
public import Aglib.RingTheory.Henselian.HenselizationNoetherian
public import Aglib.RingTheory.AdicCompletion.ApproximationTransfer

/-!
# Native-completion approximation under the intrinsic DVR condition

The actual formal-series approximation theorem is transported through the
existing canonical completion equivalence. Both the original source quotient
projection and the error in the original completed-ring ideal power are kept.
The existing affine-substitution transfer then supplies the same two precision
statements for every proper ideal, without requiring an injective comparison
between completions.

The source throughout is the actual polynomial-origin henselization. There is
no approximation premise or chosen completion equivalence, and no assertion
about an outer arbitrary finite-type local model in this leaf. The coefficient
condition is the actual canonical completed-fraction geometric reducedness.
-/

@[expose] public noncomputable section

namespace PolynomialLocalHenselization

open MvPolynomial IsLocalRing

universe u v w

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (n : ℕ)

local notation "H" => PolynomialLocalHenselization R n
local notation "Hhat" => AdicCompletion (maximalIdeal H) H

/-- Approximation in the actual native maximal-ideal completion, retaining both
literal finite quotient equality and the original extended-ideal error. This
includes order zero and independent finite equation and unknown universes. -/
theorem exists_solution_native_completion_with_precision_of_geometricallyReducedFractionCompletion
    (hcoeff : AdicCompletion.HasGeometricallyReducedFractionCompletion R)
    {σ : Type v} {ι : Type w} [Finite σ] [Finite ι]
    (F : ι → MvPolynomial σ H) (y : σ → Hhat)
    (hy : ∀ i, eval₂ (algebraMap H Hhat) y (F i) = 0) (c : ℕ) :
    ∃ x : σ → H,
      (∀ i, eval x (F i) = 0) ∧
      (∀ j, Ideal.Quotient.mk (maximalIdeal H ^ c) (x j) =
        AdicCompletion.evalₐ (maximalIdeal H) c (y j)) ∧
      ∀ j, algebraMap H Hhat (x j) - y j ∈
        (maximalIdeal H ^ c).map (algebraMap H Hhat) := by
  let e := completionFormalEquiv R n
  have he : e.toRingHom.comp (algebraMap H Hhat) = (toFormalSeries R n).toRingHom := by
    apply RingHom.ext
    intro a
    exact completionFormalEquiv_algebraMap R n a
  have hy' : ∀ i, eval₂ (toFormalSeries R n).toRingHom
      (fun j => e (y j)) (F i) = 0 := by
    intro i
    have h := congrArg e.toRingHom (hy i)
    rw [hom_eval₂, he, map_zero] at h
    exact h
  obtain ⟨x, hx, hprec⟩ :=
    exists_solution_approximation_of_geometricallyReducedFractionCompletion
      R n hcoeff F (fun j => e (y j)) hy' c
  have hq (j : σ) : Ideal.Quotient.mk (maximalIdeal H ^ c) (x j) =
      AdicCompletion.evalₐ (maximalIdeal H) c (y j) := by
    have h : AdicCompletion.evalₐ (maximalIdeal H) c (algebraMap H Hhat (x j)) =
        AdicCompletion.evalₐ (maximalIdeal H) c (y j) := by
      apply (completionFormalEquiv_sub_mem_iff R n c _ _).mp
      simpa only [completionFormalEquiv_algebraMap] using hprec j
    change AdicCompletion.evalₐ (maximalIdeal H) c
      (AdicCompletion.of (maximalIdeal H) H (x j)) = _ at h
    rwa [AdicCompletion.evalₐ_of] at h
  refine ⟨x, hx, hq, fun j => ?_⟩
  apply (native_eval_eq_iff_sub_mem R n c _ _).mp
  change AdicCompletion.evalₐ (maximalIdeal H) c
    (AdicCompletion.of (maximalIdeal H) H (x j)) = _
  rw [AdicCompletion.evalₐ_of]
  exact hq j

/-- Approximation at every proper ideal of the actual polynomial-origin
henselization under the intrinsic DVR condition. The conclusion uses the original
ideal completion, original finite quotient projection, and original completed
ideal power; the maximal-completion solver is the theorem proved above. -/
theorem exists_solution_ideal_completion_with_precision_of_geometricallyReducedFractionCompletion
    (hcoeff : AdicCompletion.HasGeometricallyReducedFractionCompletion R)
    (I : Ideal H) (hI : I ≠ ⊤)
    {σ : Type v} {ι : Type w} [Finite σ] [Finite ι]
    (F : ι → MvPolynomial σ H) (y : σ → AdicCompletion I H)
    (hy : ∀ i, eval₂ (algebraMap H (AdicCompletion I H)) y (F i) = 0) (c : ℕ) :
    ∃ x : σ → H,
      (∀ i, eval x (F i) = 0) ∧
      (∀ j, Ideal.Quotient.mk (I ^ c) (x j) = AdicCompletion.evalₐ I c (y j)) ∧
      ∀ j, algebraMap H (AdicCompletion I H) (x j) - y j ∈
        (I ^ c).map (algebraMap H (AdicCompletion I H)) := by
  let : IsNoetherianRing H := Henselization.isNoetherianRing (PolynomialLocalRing R n)
  apply AdicCompletion.exists_solution_of_larger_ideal_solver I (maximalIdeal H)
    (le_maximalIdeal hI) (IsNoetherian.noetherian I) ?_ F y hy c
  intro τ _ E z hz
  obtain ⟨x, hx, _⟩ :=
    exists_solution_native_completion_with_precision_of_geometricallyReducedFractionCompletion
      R n hcoeff E z hz 0
  exact ⟨x, hx⟩

end PolynomialLocalHenselization
