/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.FieldTheory.Units.CyclicQuotient
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.Infinite

/-!
# Descent of cyclic quotient periods under subgroup stability

Source: `R5Lab.Aglib.FieldTheory.Units.CyclicQuotientDescent`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

noncomputable section
universe u
section AlgebraicParameterDescentConstruction
universe v

/-!
# Original-field descent of the constructed finite-kernel period

All descent takes place in the literal relative algebraic closure inside the
ambient field. Stability of the given subgroup on algebraic representatives is
an explicit per-subgroup hypothesis. No fixed-field assertion for a completion,
analytic equivariance, or incoming-isogeny classification is assumed or proved.
-/

noncomputable section
namespace Units.CyclicQuotient

variable {F : Type u} {K : Type v} [Field F] [Field K] [Algebra F K]

/-- Units inclusion for the actual relative algebraic closure. -/
def algebraicUnits : (algebraicClosure F K)ˣ →* Kˣ :=
  Units.map (algebraMap (algebraicClosure F K) K).toMonoidHom

@[simp] theorem algebraicUnits_coe (x : (algebraicClosure F K)ˣ) :
    (algebraicUnits x : K) = ((x : algebraicClosure F K) : K) := rfl

theorem algebraicUnits_injective :
    Function.Injective (algebraicUnits (F := F) (K := K)) := by
  intro x y h
  apply Units.ext
  apply Subtype.ext
  exact congrArg (fun z : Kˣ => (z : K)) h

/-- The actual lift of an integral nonzero element, with no selected root. -/
def integralUnit (x : Kˣ) (hx : IsIntegral F (x : K)) :
    (algebraicClosure F K)ˣ :=
  Units.mk0 ⟨(x : K), hx⟩ (by
    intro h
    exact x.ne_zero (congrArg Subtype.val h))

@[simp] theorem algebraicUnits_integralUnit (x : Kˣ)
    (hx : IsIntegral F (x : K)) : algebraicUnits (integralUnit x hx) = x := by
  apply Units.ext
  rfl

/-- Fixed algebraic units descend through the actual algebraic closure, using
its characteristic-zero Galois theorem, rather than any completion theorem. -/
theorem algebraic_unit_descends [IsAlgClosed K] [CharZero F]
    (x : (algebraicClosure F K)ˣ)
    (hfixed : ∀ σ : (algebraicClosure F K) ≃ₐ[F] (algebraicClosure F K),
      Units.map σ.toMonoidHom x = x) :
    ∃ y : Fˣ, Units.map (algebraMap F K).toMonoidHom y = algebraicUnits x := by
  have hx : (x : algebraicClosure F K) ∈ Set.range (algebraMap F (algebraicClosure F K)) :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr fun σ =>
      congrArg (fun z : (algebraicClosure F K)ˣ => (z : algebraicClosure F K)) (hfixed σ)
  obtain ⟨y, hy⟩ := hx
  have hy0 : y ≠ 0 := by
    intro h
    subst y
    exact x.ne_zero (by simpa using hy.symm)
  refine ⟨Units.mk0 y hy0, ?_⟩
  apply Units.ext
  exact congrArg Subtype.val hy

/-- The required action contract is stated on actual algebraic representatives
of this particular subgroup of K-units modulo the original period. -/
def AlgebraicSubgroupStable (q : Fˣ)
    (H : Subgroup (QuotientGroup.CyclicQuotient (Units.map (algebraMap F K).toMonoidHom q))) :
      Prop :=
  ∀ (σ : (algebraicClosure F K) ≃ₐ[F] (algebraicClosure F K))
    (x : (algebraicClosure F K)ˣ),
    algebraicUnits x ∈ liftedSubgroup (Units.map (algebraMap F K).toMonoidHom q) H →
    algebraicUnits (Units.map σ.toMonoidHom x) ∈
      liftedSubgroup (Units.map (algebraMap F K).toMonoidHom q) H

variable (q : Fˣ)
  (hq : Function.Injective (fun z : ℤ => (Units.map (algebraMap F K).toMonoidHom q) ^ z))
  (H : Subgroup (QuotientGroup.CyclicQuotient (Units.map (algebraMap F K).toMonoidHom q)))
    [Finite H]

/-- The actual constructed generator, placed inside the algebraic closure. -/
def KernelNormalForm.algebraicGenerator
    (N : KernelNormalForm (Units.map (algebraMap F K).toMonoidHom q) hq H) :
    (algebraicClosure F K)ˣ := integralUnit (N.t : Kˣ) (N.generator_integral q hq H)

@[simp] theorem KernelNormalForm.algebraicGenerator_coe
    (N : KernelNormalForm (Units.map (algebraMap F K).toMonoidHom q) hq H) :
    algebraicUnits (N.algebraicGenerator q hq H) = (N.t : Kˣ) := by
  exact algebraicUnits_integralUnit _ _

/-- The algebraic period is the power of the very same constructed generator. -/
def KernelNormalForm.algebraicPeriod
    (N : KernelNormalForm (Units.map (algebraMap F K).toMonoidHom q) hq H) :
    (algebraicClosure F K)ˣ := (N.algebraicGenerator q hq H) ^ N.a

@[simp] theorem KernelNormalForm.algebraicPeriod_coe
    (N : KernelNormalForm (Units.map (algebraMap F K).toMonoidHom q) hq H) :
    algebraicUnits (N.algebraicPeriod q hq H) = N.p := by
  simp [KernelNormalForm.algebraicPeriod, KernelNormalForm.p]

/-- Subgroup stability fixes the constructed algebraic period. The difference
between a generator and its conjugate lies in the proved finite torsion kernel. -/
theorem KernelNormalForm.algebraicPeriod_fixed
    (N : KernelNormalForm (Units.map (algebraMap F K).toMonoidHom q) hq H)
    (hstable : AlgebraicSubgroupStable q H)
    (σ : (algebraicClosure F K) ≃ₐ[F] (algebraicClosure F K)) :
    Units.map σ.toMonoidHom (N.algebraicPeriod q hq H) = N.algebraicPeriod q hq H := by
  let qK := Units.map (algebraMap F K).toMonoidHom q
  let qA := Units.map (algebraMap F (algebraicClosure F K)).toMonoidHom q
  let tA := N.algebraicGenerator q hq H
  let σt := algebraicUnits (Units.map σ.toMonoidHom tA)
  have hqA : algebraicUnits qA = qK := by
    apply Units.ext
    rfl
  have htA : algebraicUnits tA = (N.t : Kˣ) := N.algebraicGenerator_coe q hq H
  have hσq : Units.map σ.toMonoidHom qA = qA := by
    apply Units.ext
    exact σ.commutes (q : F)
  have hpow : qA ^ periodExponent qK H N.t = tA ^ Nat.card H := by
    apply algebraicUnits_injective
    rw [map_zpow, map_pow, hqA, htA]
    exact periodExponent_spec qK H N.t
  have hσpow : σt ^ Nat.card H = (N.t : Kˣ) ^ Nat.card H := by
    have h := congrArg (fun x => algebraicUnits (Units.map σ.toMonoidHom x)) hpow
    simp only [map_zpow, map_pow, hσq, hqA] at h
    exact h.symm.trans (periodExponent_spec qK H N.t)
  have hσmem : σt ∈ liftedSubgroup qK H :=
    hstable σ tA (by rw [htA]; exact N.t.property)
  have hratio : σt / (N.t : Kˣ) ∈ torsionSubgroup qK H := by
    refine ⟨(liftedSubgroup qK H).div_mem hσmem N.t.property, ?_⟩
    change σt / (N.t : Kˣ) ∈ rootsOfUnity (Nat.card H) K
    rw [mem_rootsOfUnity, div_pow, hσpow, div_self']
  rw [N.torsion_eq, mem_rootsOfUnity, div_pow, div_eq_one] at hratio
  apply algebraicUnits_injective
  simpa only [KernelNormalForm.algebraicPeriod, map_pow,
    KernelNormalForm.algebraicGenerator_coe] using hratio

/-- The same period already produced by the normal-form construction comes
from the original field. This only consumes subgroup stability on algebraic
representatives; it does not provide that stability for an algebraic isogeny. -/
theorem KernelNormalForm.period_descends [IsAlgClosed K] [CharZero F]
    (N : KernelNormalForm (Units.map (algebraMap F K).toMonoidHom q) hq H)
    (hstable : AlgebraicSubgroupStable q H) :
    ∃ p : Fˣ, Units.map (algebraMap F K).toMonoidHom p = N.p := by
  obtain ⟨p, hp⟩ := algebraic_unit_descends (N.algebraicPeriod q hq H)
    (N.algebraicPeriod_fixed q hq H hstable)
  exact ⟨p, hp.trans (N.algebraicPeriod_coe q hq H)⟩

end Units.CyclicQuotient

end
end AlgebraicParameterDescentConstruction


/- Source cluster: DescendedParameter; source SHA256
  0196a470855f06a7455b2bcb06d306d39af0f57d3e4974f26d6321a64ccc4d4e. -/
section DescendedParameterConstruction
universe v

/-! # The constructed parameter over the original field

The chosen original-field unit maps to the existing normal-form period. Its
lattice relation and small norm are then proved over the original field itself.
The only extra input is stability of the given subgroup on algebraic representatives.
-/
noncomputable section
namespace Units.CyclicQuotient

section Field
variable {F : Type u} {K : Type v} [Field F] [Field K] [Algebra F K]
  [IsAlgClosed K] [CharZero F]
  (q : Fˣ)
  (hq : Function.Injective (fun z : ℤ => (Units.map (algebraMap F K).toMonoidHom q) ^ z))
  (H : Subgroup (QuotientGroup.CyclicQuotient (Units.map (algebraMap F K).toMonoidHom q)))
    [Finite H]
  (N : KernelNormalForm (Units.map (algebraMap F K).toMonoidHom q) hq H)
  (hstable : AlgebraicSubgroupStable q H)

/-- Original-field representative of the actual constructed normal-form period. -/
def KernelNormalForm.originalPeriod : Fˣ :=
  (N.period_descends q hq H hstable).choose

theorem KernelNormalForm.originalPeriod_map :
    Units.map (algebraMap F K).toMonoidHom (N.originalPeriod q hq H hstable) = N.p :=
  (N.period_descends q hq H hstable).choose_spec

/-- This is the period relation in the original field, with the same exponents. -/
theorem KernelNormalForm.originalPeriod_relation :
    q ^ N.a = N.originalPeriod q hq H hstable ^ N.b := by
  apply Units.map_injective (algebraMap F K).injective
  rw [map_pow, map_pow, N.originalPeriod_map]
  exact N.power_relation

/-- Descent is unique as an actual unit, not merely up to a power or valuation. -/
theorem KernelNormalForm.originalPeriod_unique (p : Fˣ)
    (hp : Units.map (algebraMap F K).toMonoidHom p = N.p) :
    p = N.originalPeriod q hq H hstable := by
  apply Units.map_injective (algebraMap F K).injective
  exact hp.trans (N.originalPeriod_map q hq H hstable).symm

end Field

end Units.CyclicQuotient

end
end DescendedParameterConstruction


/- Source cluster: AlgebraicClosureImage; source SHA256
  0f49a58d6f7578c7368264674dcff6753aff74e7f23ca512f164fd8c42bc38d9. -/
