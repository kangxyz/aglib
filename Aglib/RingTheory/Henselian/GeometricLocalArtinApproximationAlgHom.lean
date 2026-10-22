/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.ArtinApproximationAlgHom
public import Aglib.RingTheory.Henselian.GeometricLocalArtinApproximation
public import Aglib.RingTheory.Henselian.DVRGeometricLocalArtinApproximation

/-!
# Algebra-map approximation over geometric local henselizations

The proved field and characteristic-zero DVR Artin theorems apply to every
finitely presented algebra over the actual local henselization. The output
retains exact equality of the canonical quotient-valued algebra maps. Neither
flatness nor reducedness of the finite-type coefficient algebra is required.
-/

@[expose] public noncomputable section

namespace GeometricLocalHenselization

universe u v w

section Field

variable (k : Type u) [Field k] (B : Type v) [CommRing B] [Algebra k B]
  [Algebra.FiniteType k B] (q : Ideal B) [q.IsPrime]

include k in
/-- Approximate an arbitrary algebra map from a finitely presented algebra over
the actual geometric local henselization, preserving its specified quotient map. -/
theorem exists_algHom_ideal_completion_with_precision
    (I : Ideal (Henselization (Localization.AtPrime q))) (hI : I ≠ ⊤)
    (C : Type w) [CommRing C] [Algebra (Henselization (Localization.AtPrime q)) C]
    [Algebra.FinitePresentation (Henselization (Localization.AtPrime q)) C]
    (b : C →ₐ[Henselization (Localization.AtPrime q)]
      AdicCompletion I (Henselization (Localization.AtPrime q))) (n : ℕ) :
    ∃ a : C →ₐ[Henselization (Localization.AtPrime q)] Henselization (Localization.AtPrime q),
      (Ideal.Quotient.mkₐ (Henselization (Localization.AtPrime q)) (I ^ n)).comp a =
        (AdicCompletion.evalₐ I n).comp b := by
  apply Algebra.FinitePresentation.exists_algHom_with_precision_of_solver I n ?_ C b
  intro r s F y hy
  obtain ⟨x, hx, hprec, _⟩ :=
    exists_solution_ideal_completion_with_precision k B q I hI F y hy n
  exact ⟨x, hx, hprec⟩

end Field

section DVR

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R]
  (B : Type v) [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
  (q : Ideal B) [q.IsPrime]

include R in
/-- Exact algebra-map approximation over the henselization at any prime of any
finite-type algebra over a characteristic-zero DVR. The coefficient algebra
may have zero divisors and need not be flat over the DVR. -/
theorem exists_algHom_ideal_completion_with_precision_of_charZeroDVR
    (I : Ideal (Henselization (Localization.AtPrime q))) (hI : I ≠ ⊤)
    (C : Type w) [CommRing C] [Algebra (Henselization (Localization.AtPrime q)) C]
    [Algebra.FinitePresentation (Henselization (Localization.AtPrime q)) C]
    (b : C →ₐ[Henselization (Localization.AtPrime q)]
      AdicCompletion I (Henselization (Localization.AtPrime q))) (n : ℕ) :
    ∃ a : C →ₐ[Henselization (Localization.AtPrime q)] Henselization (Localization.AtPrime q),
      (Ideal.Quotient.mkₐ (Henselization (Localization.AtPrime q)) (I ^ n)).comp a =
        (AdicCompletion.evalₐ I n).comp b := by
  apply Algebra.FinitePresentation.exists_algHom_with_precision_of_solver I n ?_ C b
  intro r s F y hy
  obtain ⟨x, hx, hprec, _⟩ :=
    exists_solution_ideal_completion_with_precision_of_charZeroDVR R B q I hI F y hy n
  exact ⟨x, hx, hprec⟩

end DVR

end GeometricLocalHenselization
