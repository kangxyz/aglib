/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRoot.PowerRelation
public import Aglib.RingTheory.IntegralClosure.PureDegreePAtPrime
public import Mathlib.Algebra.Algebra.Subalgebra.IsSimpleOrder
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.RingTheory.Localization.Integral

/-!
# Integral generators in the original pure prime-degree field extension

An original nonbase element is multiplied by a nonzero original-ring
denominator. Its integral multiple remains nonbase; normality puts its pth
power in the original ring. The shared native root constructor presents the
original field extension at this same root. The normalization need not be
monogenic, and no finiteness of the normalization is assumed here.
-/

@[expose] public noncomputable section

open Polynomial
open scoped nonZeroDivisors

namespace integralClosure

variable (R K L : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [FiniteDimensional K L] [IsPurelyInseparable K L]
  (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Clear a denominator of the specified original nonbase element. The output
retains that denominator and the literal equality z = m • b. -/
theorem exists_scaled_integral_generator_of_pure_degree
    (hdegree : Module.finrank K L = p) (b : L)
    (hb : b ∉ Set.range (algebraMap K L)) :
    ∃ m : R⁰, ∃ a : R, ∃ z : integralClosure R L,
      (z : L) = m • b ∧
      (z : L) ∉ Set.range (algebraMap K L) ∧
      algebraMap R L a = (z : L) ^ p ∧
      (¬ ∃ c : K, c ^ p = algebraMap R K a) ∧
      Algebra.adjoin K {(z : L)} = ⊤ := by
  classical
  let : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (R := R) (Rₘ := K) (M := R⁰) b (Algebra.IsIntegral.isIntegral b)
  let z : integralClosure R L := ⟨m • b, hm⟩
  have hmK : algebraMap R K (m : R) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp m.property)
  have hmL : algebraMap R L (m : R) ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R K L]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).mpr hmK
  have hz : (z : L) ∉ Set.range (algebraMap K L) := by
    rintro ⟨c, hc⟩
    apply hb
    refine ⟨c / algebraMap R K (m : R), ?_⟩
    rw [map_div₀, ← IsScalarTower.algebraMap_apply R K L]
    apply (div_eq_iff hmL).mpr
    change algebraMap K L c = m • b at hc
    simpa only [Submonoid.smul_def, Algebra.smul_def, mul_comm] using hc
  obtain ⟨a, ha⟩ := pow_mem_base_of_pure_degree R K L p hdegree z
  have haL : algebraMap R L a = (z : L) ^ p := by
    exact congrArg (fun t : integralClosure R L => (t : L)) ha
  have hroot : ¬ ∃ c : K, c ^ p = algebraMap R K a := by
    rintro ⟨c, hc⟩
    apply hz
    refine ⟨c, ?_⟩
    apply frobenius_inj L p
    change (algebraMap K L c) ^ p = (z : L) ^ p
    rw [← map_pow, hc, ← IsScalarTower.algebraMap_apply R K L, haL]
  have hprime : (Module.finrank K L).Prime := by
    rw [hdegree]
    exact Fact.out
  have hgen : Algebra.adjoin K {(z : L)} = ⊤ := by
    rcases (Subalgebra.isSimpleOrder_of_finrank_prime K L hprime).eq_bot_or_eq_top
        (Algebra.adjoin K {(z : L)}) with hbot | htop
    · have hm := Algebra.self_mem_adjoin_singleton K (z : L)
      rw [hbot, Algebra.mem_bot] at hm
      exact (hz hm).elim
    · exact htop
  exact ⟨m, a, z, rfl, hz, haL, hroot, hgen⟩

/-- The field presentation is on the original field L and original coefficient
algebra K → L, with the already selected integral generator and coefficient a. -/
def pureDegreePFieldPresentation
    (hdegree : Module.finrank K L = p) (a : R) (z : integralClosure R L)
    (ha : algebraMap R L a = (z : L) ^ p)
    (hgen : Algebra.adjoin K {(z : L)} = ⊤) :
    IsAdjoinRootMonic L ((X : K[X]) ^ p - C (algebraMap R K a)) := by
  exact IsAdjoinRootMonic.ofPowerRelation (Fact.out : p.Prime).ne_zero hdegree
    (z : L) (algebraMap R K a)
    (by simpa only [IsScalarTower.algebraMap_apply R K L] using ha) hgen

omit [IsDomain R] [IsIntegrallyClosed R] [IsFractionRing R K]
  [FiniteDimensional K L] [CharP K p] in
@[simp]
theorem pureDegreePFieldPresentation_root
    (hdegree : Module.finrank K L = p) (a : R) (z : integralClosure R L)
    (ha : algebraMap R L a = (z : L) ^ p)
    (hgen : Algebra.adjoin K {(z : L)} = ⊤) :
    (pureDegreePFieldPresentation R K L p hdegree a z ha hgen).root = (z : L) :=
  IsAdjoinRootMonic.ofPowerRelation_root (Fact.out : p.Prime).ne_zero hdegree
    (z : L) (algebraMap R K a) _ hgen

omit [IsDomain R] [IsIntegrallyClosed R] [IsFractionRing R K]
  [FiniteDimensional K L] [CharP K p] in
@[simp]
theorem pureDegreePFieldPresentation_map
    (hdegree : Module.finrank K L = p) (a : R) (z : integralClosure R L)
    (ha : algebraMap R L a = (z : L) ^ p)
    (hgen : Algebra.adjoin K {(z : L)} = ⊤) :
    (pureDegreePFieldPresentation R K L p hdegree a z ha hgen).map = aeval (z : L) :=
  IsAdjoinRootMonic.ofPowerRelation_map (Fact.out : p.Prime).ne_zero hdegree
    (z : L) (algebraMap R K a) _ hgen

/-- The original prime-degree extension supplies a nonbase element, an original
nonzero denominator, and the same integral root for its original field presentation. -/
theorem exists_integral_presentation_of_pure_degree
    (hdegree : Module.finrank K L = p) :
    ∃ b : L, ∃ m : R⁰, ∃ a : R, ∃ z : integralClosure R L,
      b ∉ Set.range (algebraMap K L) ∧
      (z : L) = m • b ∧
      (z : L) ∉ Set.range (algebraMap K L) ∧
      algebraMap R L a = (z : L) ^ p ∧
      (¬ ∃ c : K, c ^ p = algebraMap R K a) ∧
      ∃ h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C (algebraMap R K a)),
        h.root = (z : L) ∧ h.map = aeval (z : L) := by
  classical
  have hns : ¬ Function.Surjective (algebraMap K L) := by
    intro hsurj
    have hdim : Module.finrank K L = 1 :=
      Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
        ⟨(algebraMap K L).injective, hsurj⟩
    exact (Fact.out : p.Prime).ne_one (hdegree.symm.trans hdim)
  have hex : ∃ b : L, b ∉ Set.range (algebraMap K L) := by
    simpa only [Function.Surjective, Set.mem_range, not_forall] using hns
  obtain ⟨b, hb⟩ := hex
  obtain ⟨m, a, z, hscale, hz, ha, hroot, hgen⟩ :=
    exists_scaled_integral_generator_of_pure_degree R K L p hdegree b hb
  let h := pureDegreePFieldPresentation R K L p hdegree a z ha hgen
  exact ⟨b, m, a, z, hb, hscale, hz, ha, hroot, h,
    pureDegreePFieldPresentation_root R K L p hdegree a z ha hgen,
    pureDegreePFieldPresentation_map R K L p hdegree a z ha hgen⟩

end integralClosure
