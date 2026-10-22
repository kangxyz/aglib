/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.DVRGeometricApproximation
public import Aglib.RingTheory.Excellent.DiscreteValuationRing

/-!
# Geometric local Artin approximation over an excellent DVR

Standard excellence supplies the intrinsic coefficient condition through its
G-ring component. The finite-type test universe of excellence is independent
of the source algebra and finite equation and unknown universes.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial

namespace GeometricLocalHenselization

universe u v w t e

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (B : Type v) [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
variable (q : Ideal B) [q.IsPrime]

include R in
/-- Full geometric local approximation over an excellent DVR, for any
prime and proper ideal, retaining the literal quotient and completion precision. -/
theorem exists_solution_ideal_completion_with_precision_of_excellentDVR
    (hexcellent : IsExcellentRing.{u, e} R)
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
  exact exists_solution_ideal_completion_with_precision_of_geometricallyReducedFractionCompletion
    R B q (IsExcellentRing.hasGeometricallyReducedFractionCompletion R hexcellent)
    I hI F y hy c

end GeometricLocalHenselization
