/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.Inertia.GaloisTame
public import Aglib.RingTheory.Henselian.FiniteDomainLocal
public import Aglib.RingTheory.Kummer.StrictHenselianUniformizer
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances

/-!
# Strictly Henselian tame normal form on the actual normalization

The original finite Galois extension with globally invertible bounded group
order gives a root chart on its literal integral closure. Locality, DVR
structure, residue equality, and the uniformizer root are derived. The chart
retains the prescribed base uniformizer and original algebra map. This is a
strictly Henselian DVR result, not étale-local descent or Abhyankar's lemma.
-/

@[expose] public noncomputable section

open IsLocalRing Algebra.Kummer

namespace integralClosure.Inertia.FiniteEtale

universe r k l

/-- The same integral closure of a strictly Henselian DVR in the original
finite Galois extension is a literal uniformizer-root algebra. The native
ramification bound is supplied by the actual Galois group order. -/
theorem exists_rootChart_of_strictHenselian_of_card_dvd_pow
    (R : Type r) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (ResidueField R)]
    (K : Type k) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type l) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n d : ℕ) (hn : IsUnit (n : R)) (hcard : Nat.card (L ≃ₐ[K] L) ∣ n ^ d)
    (π : R) (hπ : Irreducible π) :
    ∃ (e : ℕ) (E : RootAlgebra e π ≃ₐ[R] integralClosure R L),
      0 < e ∧ e ∣ n ^ d ∧ IsUnit (e : R) ∧
      Irreducible (E (AdjoinRoot.root (rootPolynomial e π))) ∧
      E (AdjoinRoot.root (rootPolynomial e π)) ^ e =
        algebraMap R (integralClosure R L) π ∧
      Module.finrank R (integralClosure R L) = e := by
  let S := integralClosure R L
  let : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  let : Module.IsTorsionFree R S := IsIntegralClosure.isTorsionFree R L
  let : Module.Finite R S := IsIntegralClosure.finite R K L S
  let : HenselianLocalRing S := HenselianLocalRing.of_finite_domain R S
  let : IsDedekindDomain S := integralClosure.isDedekindDomain R K L
  have hnotField : ¬ IsField S := fun h => IsDiscreteValuationRing.not_isField R
    (isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective R S) h)
  let : IsDiscreteValuationRing S :=
    ((IsDiscreteValuationRing.TFAE S hnotField).out 1 3).mpr
      (inferInstance : IsDedekindDomain S)
  obtain ⟨hdvd, hunit, hsep⟩ := normalization_ramification_and_residue_of_card_dvd_pow
    R K L n d hn hcard (maximalIdeal S)
  let := Localization.AtPrime.algebraOfLiesOver (maximalIdeal R) (maximalIdeal S)
  let : Algebra.IsSeparable (maximalIdeal R).ResidueField (maximalIdeal S).ResidueField := hsep
  let : Algebra.IsSeparable (ResidueField R) (ResidueField S) :=
    (Algebra.isSeparable_residueField_iff
      (p := maximalIdeal R) (q := maximalIdeal S)).mp hsep
  have hκ : Function.Surjective (algebraMap (ResidueField R) (ResidueField S)) :=
    (IsSepClosed.algebraMap_bijective (ResidueField R) (ResidueField S)).surjective
  obtain ⟨hpos, E, hirr, hpow, hrank⟩ :=
    exists_uniformizerRootEquiv_of_strictHenselian R S π hπ hκ hunit
  exact ⟨(maximalIdeal S).ramificationIdx R, E, hpos, hdvd, hunit, hirr, hpow, hrank⟩

end integralClosure.Inertia.FiniteEtale
