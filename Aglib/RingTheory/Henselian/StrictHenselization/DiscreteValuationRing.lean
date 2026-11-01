/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.StrictHenselization.LocalStages
public import Aglib.RingTheory.DiscreteValuationRing.EssentiallyEtale
public import Aglib.RingTheory.DiscreteValuationRing.SameUniformizer
public import Mathlib.RingTheory.Smooth.Flat

/-! # The original pointed etale colimit of a DVR

The specified base point must be the closed point, expressed by locality of
its field-valued map. Localizations of the existing stages at their specified
points are DVRs. Their original maps into the existing colimit are injective;
unit-power factorizations then prove that this same colimit is a DVR. No
Noetherianity of a colimit, completion, or replacement colimit is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

namespace GeometricEtaleColimit

universe u

variable (R Ω : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field Ω] [Algebra R Ω] [IsLocalHom (algebraMap R Ω)]

instance stageLocalRing_isDomain (X : GeometricEtaleNeighborhood R Ω) :
    IsDomain (stageLocalRing R Ω X) :=
  Algebra.FormallyUnramified.isDomain_of_flat_local_dvr R (stageLocalRing R Ω X)

instance stageLocalRing_isDiscreteValuationRing (X : GeometricEtaleNeighborhood R Ω) :
    IsDiscreteValuationRing (stageLocalRing R Ω X) :=
  Algebra.FormallyUnramified.isDiscreteValuationRing_of_flat_local_dvr R
    (stageLocalRing R Ω X)

/-- Every original base uniformizer is retained in each actual local stage. -/
theorem stageLocalRing_irreducible (X : GeometricEtaleNeighborhood R Ω)
    {π : R} (hπ : Irreducible π) :
    Irreducible (algebraMap R (stageLocalRing R Ω X) π) :=
  Algebra.FormallyUnramified.irreducible_algebraMap_of_flat_local_dvr R _ hπ

/-- Pointed transitions preserve the original uniformizer, hence are injective. -/
theorem stageLocalTransition_injective
    {X Y : GeometricEtaleNeighborhood R Ω} (f : X ⟶ Y) :
    Function.Injective (stageLocalTransition R Ω f) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  apply IsDiscreteValuationRing.injective_of_map_irreducible _
    (stageLocalRing_irreducible R Ω X hπ)
  rw [IsScalarTower.algebraMap_apply R X.algebra (stageLocalRing R Ω X),
    stageLocalTransition_algebraMap, AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply]
  exact stageLocalRing_irreducible R Ω Y hπ

/-- Equality in the original colimit detects equality already in the local stage. -/
theorem stageLocalMap_injective (X : GeometricEtaleNeighborhood R Ω) :
    Function.Injective (stageLocalMap R Ω X) := by
  apply (injective_iff_map_eq_zero (stageLocalMap R Ω X)).mpr
  intro x hx
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (Localization.ResiduePoint.ideal X.point.toRingHom).primeCompl x
  have ha : ι R Ω X a = 0 := by
    rw [← stageLocalMap_algebraMap]
    rw [← IsLocalization.mk'_spec (stageLocalRing R Ω X) a s, map_mul, hx, zero_mul]
  have heq : ι R Ω X a = ι R Ω X 0 := by simpa using ha
  obtain ⟨Y, f, g, hfg⟩ := (rep_eq_iff R Ω a 0).mp heq
  have hzero : f.val a = 0 := by simpa using hfg
  have ha0 : algebraMap X.algebra (stageLocalRing R Ω X) a = 0 := by
    apply stageLocalTransition_injective R Ω f
    rw [stageLocalTransition_algebraMap, hzero, map_zero, map_zero]
  apply (IsLocalization.map_units (stageLocalRing R Ω X) s).mul_right_cancel
  rw [zero_mul, IsLocalization.mk'_spec, ha0]

/-- Every nonzero colimit element has a unit-power factorization in the original
base uniformizer. -/
theorem exists_unit_mul_pow_uniformizer {π : R} (hπ : Irreducible π)
    {x : GeometricEtaleColimit R Ω} (hx : x ≠ 0) :
    ∃ (n : ℕ) (v : (GeometricEtaleColimit R Ω)ˣ),
      x = (v : GeometricEtaleColimit R Ω) * (algebraMap R _ π) ^ n := by
  obtain ⟨X, a, rfl⟩ := exists_rep R Ω x
  have ha : algebraMap X.algebra (stageLocalRing R Ω X) a ≠ 0 := by
    intro h
    apply hx
    rw [← stageLocalMap_algebraMap, h, map_zero]
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha
    (stageLocalRing_irreducible R Ω X hπ)
  refine ⟨n, Units.map (stageLocalMap R Ω X).toMonoidHom v, ?_⟩
  change ι R Ω X a = stageLocalMap R Ω X (v : stageLocalRing R Ω X) *
    (algebraMap R (GeometricEtaleColimit R Ω) π) ^ n
  have h := congrArg (stageLocalMap R Ω X) hv
  simpa only [stageLocalMap_algebraMap, map_mul, map_pow, AlgHom.commutes] using h

/-- The original base uniformizer has nonzero powers in the unchanged colimit. -/
theorem uniformizer_pow_ne_zero {π : R} (hπ : Irreducible π) (n : ℕ) :
    (algebraMap R (GeometricEtaleColimit R Ω) π) ^ n ≠ 0 := by
  let X : GeometricEtaleNeighborhood R Ω := Classical.choice inferInstance
  have h := pow_ne_zero n (stageLocalRing_irreducible R Ω X hπ).ne_zero
  intro hz
  apply h
  apply stageLocalMap_injective R Ω X
  simpa only [map_pow, AlgHom.commutes, map_zero] using hz

/-- The original neighborhood colimit is a domain, proved from retained
uniformizer powers and actual stage factorizations. -/
theorem isDomain_of_dvr : IsDomain (GeometricEtaleColimit R Ω) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let : NoZeroDivisors (GeometricEtaleColimit R Ω) := ⟨by
    intro x y hxy
    by_contra! h
    obtain ⟨n, v, rfl⟩ := exists_unit_mul_pow_uniformizer R Ω hπ h.1
    obtain ⟨m, w, rfl⟩ := exists_unit_mul_pow_uniformizer R Ω hπ h.2
    have he : (v : GeometricEtaleColimit R Ω) * (algebraMap R _ π) ^ n *
        ((w : GeometricEtaleColimit R Ω) * (algebraMap R _ π) ^ m) =
        (v * w : (GeometricEtaleColimit R Ω)ˣ) * (algebraMap R _ π) ^ (n + m) := by
      simp only [Units.val_mul, pow_add]
      ac_rfl
    rw [he] at hxy
    exact uniformizer_pow_ne_zero R Ω hπ (n + m)
      ((v * w).isUnit.mul_right_eq_zero.mp hxy)⟩
  exact NoZeroDivisors.to_isDomain _

/-- The original base uniformizer generates the actual maximal ideal. -/
theorem maximalIdeal_eq_span_uniformizer {π : R} (hπ : Irreducible π) :
    maximalIdeal (GeometricEtaleColimit R Ω) =
      Ideal.span {algebraMap R (GeometricEtaleColimit R Ω) π} := by
  have hp : ¬ IsUnit (algebraMap R (GeometricEtaleColimit R Ω) π) := by
    intro h
    apply hπ.not_isUnit
    apply isUnit_of_map_unit (algebraMap R Ω) π
    simpa only [AlgHom.commutes] using h.map (residue R Ω)
  apply le_antisymm
  · intro x hx
    by_cases hzero : x = 0
    · simpa only [hzero] using (Ideal.span {algebraMap R (GeometricEtaleColimit R Ω) π}).zero_mem
    obtain ⟨n, v, rfl⟩ := exists_unit_mul_pow_uniformizer R Ω hπ hzero
    cases n with
    | zero => exact False.elim (hx (by simp))
    | succ n =>
      apply Ideal.mem_span_singleton.mpr
      exact ⟨(v : GeometricEtaleColimit R Ω) * (algebraMap R _ π) ^ n, by
        rw [pow_succ]; ring⟩
  · exact (Ideal.span_singleton_le_iff_mem _).mpr hp

/-- Every original uniformizer remains irreducible in the original colimit. -/
theorem irreducible_algebraMap_of_dvr {π : R} (hπ : Irreducible π) :
    Irreducible (algebraMap R (GeometricEtaleColimit R Ω) π) := by
  let := isDomain_of_dvr R Ω
  exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    (by simpa using uniformizer_pow_ne_zero R Ω hπ 1)
    (maximalIdeal_eq_span_uniformizer R Ω hπ)

/-- At the specified closed point, the original geometric etale colimit is a DVR.
No separable-closedness assumption on the specified field is required. -/
theorem isDiscreteValuationRing_of_dvr :
    letI := isDomain_of_dvr R Ω
    IsDiscreteValuationRing (GeometricEtaleColimit R Ω) := by
  let := isDomain_of_dvr R Ω
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨algebraMap R _ π, irreducible_algebraMap_of_dvr R Ω hπ, ?_⟩
  intro x hx
  obtain ⟨n, v, rfl⟩ := exists_unit_mul_pow_uniformizer R Ω hπ hx
  exact ⟨n, ⟨v, by simp [mul_comm]⟩⟩

end GeometricEtaleColimit
