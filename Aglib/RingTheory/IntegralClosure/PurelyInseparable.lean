/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.CompleteCurve
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Purely inseparable normalization of a DVR

The literal integral closure of a DVR in a finite purely inseparable
extension of its fraction field is a Noetherian DVR. Its original residue
field extension is finite. No completeness or module finiteness of the
normalization over the base DVR is assumed.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors Pointwise

namespace integralClosure

variable (A K E : Type*) [CommRing A] [IsDomain A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]

include K

private theorem base_injective : Function.Injective (algebraMap A (integralClosure A E)) := by
  let : Module.IsTorsionFree A E := .trans_faithfulSMul A K E
  let : Module.IsTorsionFree A (integralClosure A E) := IsIntegralClosure.isTorsionFree A E
  exact FaithfulSMul.algebraMap_injective A (integralClosure A E)

/-- The original coefficient map to its literal integral closure reflects
units. This does not require completeness or finite generation. -/
theorem algebraMap_isLocalHom : IsLocalHom (algebraMap A (integralClosure A E)) := by
  let : Algebra.IsIntegral A (integralClosure A E) := IsIntegralClosure.isIntegral_algebra A E
  exact (algebraMap_isIntegral_iff.mpr inferInstance).isLocalHom (base_injective A K E)

omit [IsDomain A] in
/-- Over a normal base, a positive power lying in the fraction field
detects membership in the literal normalization through the original map. -/
theorem mem_iff_pow_mem_range [IsIntegrallyClosed A] (u : E) (n : ℕ) (hn : 0 < n)
    (hK : u ^ n ∈ (algebraMap K E).range) :
    u ∈ integralClosure A E ↔ u ^ n ∈ (algebraMap A E).range := by
  change IsIntegral A u ↔ _
  constructor
  · intro hu
    obtain ⟨k, hk⟩ := hK
    have hkint : IsIntegral A k := by
      apply (isIntegral_algebraMap_iff (R := A) (A := K) (B := E)).mp
      rw [hk]
      exact hu.pow n
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hkint
    refine ⟨a, ?_⟩
    rw [IsScalarTower.algebraMap_apply A K E, ha, hk]
  · rintro ⟨a, ha⟩
    apply IsIntegral.of_pow hn
    rw [← ha]
    exact isIntegral_algebraMap

variable [FiniteDimensional K E]

omit [IsDomain A] in
private theorem normalization_rank_lt_aleph0 :
    Module.rank A (integralClosure A E) < Cardinal.aleph0 := by
  apply lt_of_le_of_lt
    ((integralClosure A E).val.toLinearMap.rank_le_of_injective Subtype.val_injective)
  rw [← IsFractionRing.rank_right_eq A K E]
  exact Module.rank_lt_aleph0 K E

/-- Integral normalization of a DVR in any finite fraction-field extension
is Noetherian as a ring. This is not module finiteness over the DVR. -/
theorem isNoetherianRing_of_isDiscreteValuationRing [IsDiscreteValuationRing A] :
    IsNoetherianRing (integralClosure A E) := by
  let : Module.IsTorsionFree A (integralClosure A E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (base_injective A K E)
  let : Algebra.IsIntegral A (integralClosure A E) := IsIntegralClosure.isIntegral_algebra A E
  exact Algebra.IsIntegral.isNoetherianRing_of_rank_lt_aleph0
    (normalization_rank_lt_aleph0 A K E)

variable [IsPurelyInseparable K E]

/-- Normalization of a valuation domain in a finite purely inseparable
fraction-field extension is a valuation domain through the actual embedding. -/
theorem valuationRing_of_isPurelyInseparable [ValuationRing A] :
    ValuationRing (integralClosure A E) := by
  let : IsFractionRing (integralClosure A E) E := isFractionRing_of_finite_extension K E
  apply (ValuationRing.iff_isInteger_or_isInteger (integralClosure A E) E).mpr
  obtain ⟨e, he⟩ := (inferInstance : IsPurelyInseparable.HasExponent K E).has_exponent
  have hq : 0 < ringExpChar K ^ e := by
    apply pow_pos
    unfold ringExpChar
    exact lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  intro u
  obtain ⟨k, hk⟩ := he u
  rcases ValuationRing.isInteger_or_isInteger A k with ⟨a, ha⟩ | ⟨a, ha⟩
  · have hu : u ∈ integralClosure A E := by
      change IsIntegral A u
      apply IsIntegral.of_pow hq
      rw [← hk, ← ha, ← IsScalarTower.algebraMap_apply A K E]
      exact isIntegral_algebraMap
    exact Or.inl ⟨⟨u, hu⟩, rfl⟩
  · have hu : u⁻¹ ∈ integralClosure A E := by
      change IsIntegral A u⁻¹
      apply IsIntegral.of_pow hq
      rw [inv_pow, ← hk, ← map_inv₀, ← ha, ← IsScalarTower.algebraMap_apply A K E]
      exact isIntegral_algebraMap
    exact Or.inr ⟨⟨u⁻¹, hu⟩, rfl⟩

/-- The literal normalization of a DVR in a finite purely inseparable
extension is a DVR. No completeness or Japanese-ring premise is imposed. -/
theorem isDiscreteValuationRing_of_isPurelyInseparable [IsDiscreteValuationRing A] :
    IsDiscreteValuationRing (integralClosure A E) := by
  let : IsNoetherianRing (integralClosure A E) :=
    isNoetherianRing_of_isDiscreteValuationRing A K E
  let : ValuationRing (integralClosure A E) := valuationRing_of_isPurelyInseparable A K E
  let : Algebra.IsIntegral A (integralClosure A E) := IsIntegralClosure.isIntegral_algebra A E
  have hnot : ¬ IsField (integralClosure A E) := fun h ↦
    IsDiscreteValuationRing.not_isField A
      (isField_of_isIntegral_of_isField (base_injective A K E) h)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure A E) hnot).out 2 1).mp
    (inferInstance : ValuationRing (integralClosure A E))

variable [IsDiscreteValuationRing A]

/-- The native residue-field algebra induced by the original local map
from the DVR to its purely inseparable normalization. -/
@[instance_reducible]
def purelyInseparableResidueAlgebra :
    let _ : IsDiscreteValuationRing (integralClosure A E) :=
      isDiscreteValuationRing_of_isPurelyInseparable A K E
    Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField (integralClosure A E)) := by
  let : IsDiscreteValuationRing (integralClosure A E) :=
    isDiscreteValuationRing_of_isPurelyInseparable A K E
  let : IsLocalHom (algebraMap A (integralClosure A E)) := algebraMap_isLocalHom A K E
  infer_instance

/-- The residue coefficient map is the actual one induced by the original
coefficient map into the normalization. -/
theorem purelyInseparableResidueAlgebra_residue (a : A) :
    let _ : IsDiscreteValuationRing (integralClosure A E) :=
      isDiscreteValuationRing_of_isPurelyInseparable A K E
    let _ := purelyInseparableResidueAlgebra A K E
    algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField (integralClosure A E))
        (IsLocalRing.residue A a) =
      IsLocalRing.residue (integralClosure A E) (algebraMap A (integralClosure A E) a) := by
  let : IsDiscreteValuationRing (integralClosure A E) :=
    isDiscreteValuationRing_of_isPurelyInseparable A K E
  let : IsLocalHom (algebraMap A (integralClosure A E)) := algebraMap_isLocalHom A K E
  exact IsLocalRing.ResidueField.algebraMap_residue (R := A) (S := integralClosure A E) a

/-- The canonical residue-field extension is finite, proved from a scalar
quotient. Finiteness of the normalization as an A-module is not assumed. -/
theorem finite_residueField_of_isPurelyInseparable :
    let _ : IsDiscreteValuationRing (integralClosure A E) :=
      isDiscreteValuationRing_of_isPurelyInseparable A K E
    let _ := purelyInseparableResidueAlgebra A K E
    Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField (integralClosure A E)) := by
  let : IsDiscreteValuationRing (integralClosure A E) :=
    isDiscreteValuationRing_of_isPurelyInseparable A K E
  let : IsLocalHom (algebraMap A (integralClosure A E)) := algebraMap_isLocalHom A K E
  let : Algebra (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField (integralClosure A E)) := purelyInseparableResidueAlgebra A K E
  change Module.Finite (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField (integralClosure A E))
  let S := integralClosure A E
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπm : π ∈ IsLocalRing.maximalIdeal A := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hπ.not_isUnit
  have hzero : algebraMap A (IsLocalRing.ResidueField S) π = 0 := by
    rw [IsScalarTower.algebraMap_apply A S (IsLocalRing.ResidueField S),
      IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
    exact _root_.map_nonunit (algebraMap A S) π hπm
  let f : S →ₗ[A] IsLocalRing.ResidueField S :=
    (Algebra.linearMap S (IsLocalRing.ResidueField S)).restrictScalars A
  have hker : π • (⊤ : Submodule A S) ≤ LinearMap.ker f := by
    intro s hs
    obtain ⟨t, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hs
    change f (π • t) = 0
    rw [map_smul, Algebra.smul_def, hzero, zero_mul]
  let g : QuotSMulTop π S →ₗ[A] IsLocalRing.ResidueField S :=
    (π • (⊤ : Submodule A S)).liftQ f hker
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨s, hs⟩ := IsLocalRing.residue_surjective (R := S) z
    refine ⟨Submodule.Quotient.mk s, ?_⟩
    change algebraMap S (IsLocalRing.ResidueField S) s = z
    exact hs
  let : Module.IsTorsionFree A S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (base_injective A K E)
  have hlength := QuotSMulTop.isFiniteLength_of_rank_lt_aleph0
    (normalization_rank_lt_aleph0 A K E) π hπ.ne_zero
  have hres : IsFiniteLength A (IsLocalRing.ResidueField S) := hlength.of_surjective hg
  let : IsNoetherian A (IsLocalRing.ResidueField S) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hres).1
  exact Module.Finite.of_restrictScalars_finite A (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField S)

end integralClosure
