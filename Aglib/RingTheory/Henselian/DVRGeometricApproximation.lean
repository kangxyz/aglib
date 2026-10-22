/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.DVRGeometricFiniteModelCoefficient
public import Aglib.RingTheory.Henselian.GenericGeometricLocalArtinApproximation
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationDVRFiniteLocalApproximation
public import Aglib.RingTheory.AdicCompletion.RingEquivApproximation
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Geometric local Artin approximation under the intrinsic DVR condition

For any prime of an arbitrary finite-type algebra over the coefficient DVR,
the actual localization henselization admits approximation at any proper ideal.
The generic branch uses the existing field theorem; the vertical branch uses
the native parameter DVR with its proved completion condition and the shared
finite-local transfer. Both precision conditions refer to the original ring.
-/

@[expose] public noncomputable section

open IsLocalRing DVRGeometricLocalHenselization MvPolynomial

namespace GeometricLocalHenselization

universe u v w t

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (B : Type v) [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
variable (q : Ideal B) [q.IsPrime]

include R in
/-- Full geometric local approximation under the intrinsic DVR condition, for any
prime and proper ideal, retaining the literal quotient and completion precision. -/
theorem exists_solution_ideal_completion_with_precision_of_geometricallyReducedFractionCompletion
    (hcoeff : AdicCompletion.HasGeometricallyReducedFractionCompletion R)
    (I : Ideal (Henselization (Localization.AtPrime q))) (hI : I ≠ ⊤)
    {σ : Type w} {ι : Type t} [Finite σ] [Finite ι]
    (F : ι → MvPolynomial σ (Henselization (Localization.AtPrime q)))
    (y : σ → AdicCompletion I (Henselization (Localization.AtPrime q)))
    (hy : ∀ i, eval₂
      (algebraMap (Henselization (Localization.AtPrime q))
        (AdicCompletion I (Henselization (Localization.AtPrime q)))) y (F i) = 0)
    (c : ℕ) :
    ∃ x : σ → Henselization (Localization.AtPrime q),
      (∀ i, eval x (F i) = 0) ∧
      (∀ j, Ideal.Quotient.mk (I ^ c) (x j) = AdicCompletion.evalₐ I c (y j)) ∧
      ∀ j, algebraMap (Henselization (Localization.AtPrime q))
        (AdicCompletion I (Henselization (Localization.AtPrime q))) (x j) - y j ∈
        (I ^ c).map (algebraMap (Henselization (Localization.AtPrime q))
          (AdicCompletion I (Henselization (Localization.AtPrime q)))) := by
  classical
  by_cases hqzero : q.comap (algebraMap R B) = ⊥
  · exact GenericGeometricLocalHenselization.exists_solution_ideal_completion_with_precision
      R B q hqzero I hI F y hy c
  · have hqmax : q.comap (algebraMap R B) = maximalIdeal R :=
      eq_maximalIdeal (IsPrime.to_maximal_ideal hqzero)
    obtain ⟨S, hS, hSDomain, hSDVR, aS, _hRS, hcoeffS,
      n, A, hA, aA, fA, lA, ⟨e⟩⟩ :=
      exists_finite_origin_model_of_geometricallyReducedFractionCompletion
        R B q hqmax hcoeff
    let := hS
    let := hSDomain
    let := hSDVR
    let := aS
    let := hA
    let := aA
    let := fA
    let := lA
    have hJ : I.map e.toRingHom ≠ ⊤ := AdicCompletion.map_ne_top_of_ringEquiv e I hI
    refine AdicCompletion.exists_solution_of_ringEquiv_solver e I ?_ F y hy c
    intro E s hs d
    open PolynomialLocalHenselization in
    exact exists_solution_finite_local_ideal_completion_with_precision_of_fractionCompletion
      S n hcoeffS A (I.map e.toRingHom) hJ E s hs d

end GeometricLocalHenselization
