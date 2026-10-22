/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.DVRGeometricFiniteModel
public import Aglib.RingTheory.Henselian.GenericGeometricLocalArtinApproximation
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationCharZeroDVRFiniteLocalApproximation
public import Aglib.RingTheory.AdicCompletion.RingEquivApproximation
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Geometric local Artin approximation over a characteristic-zero DVR

For an arbitrary prime of an arbitrary finite-type algebra over a
characteristic-zero DVR, the actual henselization of the prime localization
admits approximation at every proper ideal. The generic branch uses the actual
fraction-base localization and the proved field theorem. The vertical branch
uses the constructed common-universe finite local model over the actual
parameter DVR. Its injective coefficient map transports characteristic zero
of the original DVR, without requiring it of the source algebra or the residue
field. The actual completion equivalence returns both original precision
conditions to the original henselization. No solver or model premise remains.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial

namespace GeometricLocalHenselization

universe u v w t

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R]
variable (B : Type v) [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
variable (q : Ideal B) [q.IsPrime]

include R in
/-- Full geometric local approximation over a characteristic-zero DVR, for any
prime and proper ideal, retaining the literal quotient and completion precision. -/
theorem exists_solution_ideal_completion_with_precision_of_charZeroDVR
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
    obtain ⟨S, hS, hSDomain, hSDVR, aS, hRS, n, A, hA, aA, fA, lA, ⟨e⟩⟩ :=
      DVRGeometricLocalHenselization.exists_finite_origin_model R B q hqmax
    let := hS
    let := hSDomain
    let := hSDVR
    let := aS
    let : CharZero S := charZero_of_injective_algebraMap hRS
    let := hA
    let := aA
    let := fA
    let := lA
    have hJ : I.map e.toRingHom ≠ ⊤ := AdicCompletion.map_ne_top_of_ringEquiv e I hI
    refine AdicCompletion.exists_solution_of_ringEquiv_solver e I ?_ F y hy c
    intro E s hs d
    open PolynomialLocalHenselization in
    exact exists_solution_finite_local_ideal_completion_with_precision_of_charZeroDVR
      S n A (I.map e.toRingHom) hJ E s hs d

end GeometricLocalHenselization
