/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteLength.Torsion
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Colength of a finite normalization in dimension at most one

The quotient of the literal integral closure by the original coefficient map
is torsion because each element has a denominator in the original ring.
If that normalization is finite and the base is Noetherian of dimension at
most one, the quotient therefore has finite length. The total quotient ring
is allowed: no domain, reducedness, locality or separability is assumed.

Finiteness of normalization is an explicit premise of the length theorem.
This module does not prove the excellence or Nagata theorem that supplies it.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace integralClosure

variable (R Q : Type*) [CommRing R] [CommRing Q]
  [Algebra R Q] [IsFractionRing R Q]

/-- The actual quotient by the original ring is torsion in its total quotient
ring, without a finiteness or domain assumption. -/
theorem quotient_isTorsion :
    Module.IsTorsion R
      (integralClosure R Q ⧸ LinearMap.range (Algebra.linearMap R (integralClosure R Q))) := by
  intro z
  obtain ⟨b, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.range (Algebra.linearMap R (integralClosure R Q))) z
  obtain ⟨⟨r, s⟩, hs⟩ := IsLocalization.surj R⁰ (b : Q)
  refine ⟨s, ?_⟩
  change (s : R) •
    ((LinearMap.range (Algebra.linearMap R (integralClosure R Q))).mkQ b) = 0
  rw [← map_smul]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨r, ?_⟩
  apply Subtype.ext
  rw [Algebra.linearMap_apply, Subalgebra.coe_algebraMap,
    Subalgebra.coe_smul, Algebra.smul_def]
  exact ((mul_comm (algebraMap R Q (s : R)) (b : Q)).trans hs).symm

/-- A finite actual normalization has finite colength in dimension at most
one. This applies unchanged to reduced rings with several components. -/
theorem quotient_isFiniteLength [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [Module.Finite R (integralClosure R Q)] :
    IsFiniteLength R
      (integralClosure R Q ⧸ LinearMap.range (Algebra.linearMap R (integralClosure R Q))) :=
  Module.finiteLength_of_isTorsion (quotient_isTorsion R Q)

/-- The normalization-colength bound is a finite extended natural number. -/
theorem quotient_length_ne_top [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [Module.Finite R (integralClosure R Q)] :
    Module.length R
      (integralClosure R Q ⧸ LinearMap.range (Algebra.linearMap R (integralClosure R Q))) ≠ ⊤ :=
  Module.length_ne_top_iff.mpr (quotient_isFiniteLength R Q)

section OriginalBase

variable (A : Type*) [CommRing A] [Algebra A R] [Algebra A Q]
  [IsScalarTower A R Q]

omit [IsFractionRing R Q] in
/-- For a surjective original coefficient map, its image in the normalization
is exactly the image of the quotient ring with scalars restricted. -/
theorem range_restrictScalars_of_surjective
    (hsurj : Function.Surjective (algebraMap A R)) :
    (LinearMap.range (Algebra.linearMap R (integralClosure R Q))).restrictScalars A =
      LinearMap.range (Algebra.linearMap A (integralClosure R Q)) := by
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨a, rfl⟩ := hsurj r
    exact ⟨a, IsScalarTower.algebraMap_apply A R (integralClosure R Q) a⟩
  · rintro ⟨a, rfl⟩
    exact ⟨algebraMap A R a,
      (IsScalarTower.algebraMap_apply A R (integralClosure R Q) a).symm⟩

/-- The finite normalization colength is measured over the original ring,
using its original map to the normalization. In the divisor application,
`R` is the actual quotient of `A` by the divisor equation. -/
theorem quotient_original_length_ne_top [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [Module.Finite R (integralClosure R Q)]
    (hsurj : Function.Surjective (algebraMap A R)) :
    Module.length A
      (integralClosure R Q ⧸ LinearMap.range (Algebra.linearMap A (integralClosure R Q))) ≠ ⊤ := by
  rw [← range_restrictScalars_of_surjective R Q A hsurj]
  change Module.length A
    (integralClosure R Q ⧸ LinearMap.range (Algebra.linearMap R (integralClosure R Q))) ≠ ⊤
  rw [Module.length_eq_of_surjective hsurj]
  exact quotient_length_ne_top R Q

end OriginalBase

end integralClosure
