/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.Inertia.TameDegree
public import Aglib.RingTheory.IntegralClosure.Inertia.Horizontal

/-! # Original finite Galois normalization at invertible-order primes

The canonical action of the original field Galois group on the actual integral
closure supplies the invariant finite flat ring extension. An annihilator-power
bound on that actual group order gives ramification-index divisibility and
invertibility in the original DVR, and separability of the original residue map.
No ring action, residue separability, perfectness or characteristic-zero premise
is supplied. This does not construct tame normal-form charts.
-/

@[expose] public noncomputable section

namespace integralClosure.Inertia.FiniteEtale

universe r k l

variable (R : Type r) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type k) [Field K] [Algebra R K] [IsFractionRing R K]
  (L : Type l) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- An original finite Galois extension with annihilator-power order has the
actual ramification bound, globally invertible ramification index, and separable
residue extension at every chosen prime of its literal normalization. -/
theorem normalization_ramification_and_residue_of_card_dvd_pow
    (n d : ℕ) (hn : IsUnit (n : R))
    (hcard : Nat.card (L ≃ₐ[K] L) ∣ n ^ d)
    (P : Ideal (integralClosure R L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal R)] :
    P.ramificationIdx R ∣ n ^ d ∧ IsUnit (P.ramificationIdx R : R) ∧
      (letI := Localization.AtPrime.algebraOfLiesOver (IsLocalRing.maximalIdeal R) P
       Algebra.IsSeparable (IsLocalRing.maximalIdeal R).ResidueField P.ResidueField) := by
  let : IsGaloisGroup (L ≃ₐ[K] L) R (integralClosure R L) :=
    Horizontal.model_isGaloisGroup R K L
  let : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
  let : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  let : Module.Free R (integralClosure R L) := IsIntegralClosure.module_free R K L _
  have he : P.ramificationIdx R ∣ n ^ d :=
    (ramificationIdx_dvd_card R (integralClosure R L) (L ≃ₐ[K] L)
      (IsLocalRing.maximalIdeal R) P).trans hcard
  have hpow : IsUnit ((n ^ d : ℕ) : R) := by
    simpa only [Nat.cast_pow] using hn.pow d
  have heunit : IsUnit (P.ramificationIdx R : R) := by
    apply isUnit_of_dvd_unit _ hpow
    obtain ⟨a, ha⟩ := he
    exact ⟨(a : R), by rw [ha, Nat.cast_mul]⟩
  have hGunit : IsUnit (Nat.card (L ≃ₐ[K] L) : R) := by
    apply isUnit_of_dvd_unit _ hpow
    obtain ⟨a, ha⟩ := hcard
    exact ⟨(a : R), by rw [ha, Nat.cast_mul]⟩
  refine ⟨he, heunit, ?_⟩
  apply residue_isSeparable_of_isUnit_card R (integralClosure R L) (L ≃ₐ[K] L)
    (IsLocalRing.maximalIdeal R) P
  simpa only [map_natCast] using
    hGunit.map (algebraMap R (IsLocalRing.maximalIdeal R).ResidueField)

end integralClosure.Inertia.FiniteEtale
