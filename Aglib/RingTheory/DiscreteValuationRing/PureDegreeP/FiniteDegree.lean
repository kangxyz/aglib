/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Finite DVR degree and the actual pth-power coefficients

Uncompiled authoring for the next R.B5 algebra leaf. Finiteness, rather than
a defectless premise, supplies the degree formula. All fields and rings use
their original algebra maps. This file does not construct a differential trace.
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial

namespace IsDiscreteValuationRing

section FiniteDegree

variable (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]

/-- In a finite extension of DVRs the actual ramification and residue degrees
multiply to the original module rank. No separability is used. -/
theorem ramification_mul_residue_finrank_eq_finrank :
    (maximalIdeal B).ramificationIdx A *
      Module.finrank (ResidueField A) (ResidueField B) = Module.finrank A B := by
  classical
  let : Module.Free A B := Module.free_of_finite_type_torsion_free'
  let : IsLocalHom (algebraMap A B) := inferInstance
  let q : (maximalIdeal A).primesOver B := Ideal.primesOver.mk _ (maximalIdeal B)
  have hmax (t : (maximalIdeal A).primesOver B) : (t : Ideal B) = maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (Ideal.primesOver.isMaximal t)
  let : Unique ((maximalIdeal A).primesOver B) :=
    { default := q
      uniq t := Subtype.ext (hmax t) }
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (maximalIdeal A) B
  have hsingle : (maximalIdeal B).ramificationIdx A *
      (maximalIdeal B).inertiaDeg A = Module.finrank A B := by
    simpa only [Finset.univ_unique, Finset.sum_singleton, hmax] using hsum
  have hinertia := Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal A) (maximalIdeal B)
  change (maximalIdeal B).inertiaDeg A =
    Module.finrank (ResidueField A) (ResidueField B) at hinertia
  rwa [hinertia] at hsingle

/-- The native ramification index is the literal exponent in the image of
the original uniformizer. This comparison is derived, not an extra index premise. -/
theorem ramificationIdx_eq_uniformizerExponent
    {π : A} {τ : B} (hπ : Irreducible π) (hτ : Irreducible τ)
    (u : Bˣ) (e : ℕ) (he : algebraMap A B π = (u : B) * τ ^ e) :
    (maximalIdeal B).ramificationIdx A = e := by
  let : IsLocalHom (algebraMap A B) := inferInstance
  have hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B ^ e := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, he,
      Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hτ.maximalIdeal_eq]
  have hA : maximalIdeal A ≠ ⊥ := by
    rw [hπ.maximalIdeal_eq, ne_eq, Ideal.span_singleton_eq_bot]
    exact hπ.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal A) (maximalIdeal B) hA]
  apply Ideal.ramificationIdx'_spec
  · exact hm.le
  · rw [hm]
    intro hle
    have hvalue (n : ℕ) : idealOrderIsoENat B (maximalIdeal B ^ n) =
        OrderDual.toDual (n : ℕ∞) := by
      rw [← idealOrderIsoENat_symm_apply_coe B n]
      exact (idealOrderIsoENat B).apply_symm_apply (OrderDual.toDual (n : ℕ∞))
    have hbad := (idealOrderIsoENat B).monotone hle
    rw [hvalue, hvalue] at hbad
    change (e + 1 : ℕ∞) ≤ e at hbad
    have hnat : e + 1 ≤ e := by exact_mod_cast hbad
    exact (Nat.not_succ_le_self e) hnat

/-- Finiteness proves the literal `e*f` equality for the actual fraction fields. -/
theorem uniformizerExponent_mul_residue_finrank_eq
    (K L : Type*) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    {π : A} {τ : B} (hπ : Irreducible π) (hτ : Irreducible τ)
    (u : Bˣ) (e : ℕ) (he : algebraMap A B π = (u : B) * τ ^ e) :
    e * Module.finrank (ResidueField A) (ResidueField B) = Module.finrank K L := by
  rw [← ramificationIdx_eq_uniformizerExponent A B hπ hτ u e he,
    ramification_mul_residue_finrank_eq_finrank]
  exact (IsFractionRing.finrank_eq A K B L).symm

/-- In prime generic degree these are the two actual ramification/residue cases. -/
theorem uniformizerExponent_residue_cases
    (K L : Type*) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    {p : ℕ} (hp : p.Prime) (hdegree : Module.finrank K L = p)
    {π : A} {τ : B} (hπ : Irreducible π) (hτ : Irreducible τ)
    (u : Bˣ) (e : ℕ) (he : algebraMap A B π = (u : B) * τ ^ e) :
    (e = p ∧ Module.finrank (ResidueField A) (ResidueField B) = 1) ∨
      (e = 1 ∧ Module.finrank (ResidueField A) (ResidueField B) = p) := by
  have hef : e * Module.finrank (ResidueField A) (ResidueField B) = p :=
    (uniformizerExponent_mul_residue_finrank_eq A B K L hπ hτ u e he).trans hdegree
  have hprime : (e * Module.finrank (ResidueField A) (ResidueField B)).Prime := by
    rwa [hef]
  rcases Nat.prime_mul_iff.mp hprime with h | h
  · exact Or.inl ⟨by simpa only [h.2, mul_one] using hef, h.2⟩
  · exact Or.inr ⟨h.2, by simpa only [h.2, one_mul] using hef⟩

end FiniteDegree

end IsDiscreteValuationRing

namespace IsPurelyInseparable

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsPurelyInseparable K L]
  (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Prime generic degree forces exponent at most one for every original element. -/
theorem pow_mem_range_of_finrank_eq_prime (hdegree : Module.finrank K L = p) (x : L) :
    x ^ p ∈ (algebraMap K L).range := by
  have hp : p.Prime := Fact.out
  have hle : p ^ elemExponent K x ≤ p := by
    rw [← minpoly_natDegree_eq' K p x, ← hdegree]
    exact minpoly.natDegree_le x
  have hexp : elemExponent K x ≤ 1 :=
    (pow_le_pow_iff_right₀ hp.one_lt).mp (by simpa only [pow_one] using hle)
  obtain ⟨c, hc⟩ := elemExponent_def' K p x
  by_cases hz : elemExponent K x = 0
  · have hcx : algebraMap K L c = x := by simpa only [hz, pow_zero, pow_one] using hc
    exact ⟨c ^ p, by rw [map_pow, hcx]⟩
  · have ho : elemExponent K x = 1 := by omega
    exact ⟨c, by simpa only [ho, pow_one] using hc⟩

end IsPurelyInseparable

namespace IsDiscreteValuationRing

variable (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra B L] [IsFractionRing B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  [FiniteDimensional K L] [IsPurelyInseparable K L]
  (p : ℕ) [Fact p.Prime] [CharP K p]

omit [IsDomain B] in
/-- Original normality descends each actual pth power from the fraction field to A. -/
theorem exists_algebraMap_eq_pow_of_finite_pure_degree
    (hdegree : Module.finrank K L = p) (b : B) :
    ∃ a : A, algebraMap A B a = b ^ p := by
  obtain ⟨k, hk⟩ :=
    IsPurelyInseparable.pow_mem_range_of_finrank_eq_prime K L p hdegree (algebraMap B L b)
  have hb0 : IsIntegral A b := Algebra.IsIntegral.isIntegral b
  have hb : IsIntegral A (algebraMap B L b) :=
    hb0.map (IsScalarTower.toAlgHom A B L)
  have hkint : IsIntegral A k := by
    apply (isIntegral_algebraMap_iff (R := A) (A := K) (B := L)).mp
    rw [hk]
    exact hb.pow p
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hkint
  refine ⟨a, ?_⟩
  apply IsFractionRing.injective B L
  rw [map_pow, ← IsScalarTower.algebraMap_apply A B L,
    IsScalarTower.algebraMap_apply A K L, ha, hk]

end IsDiscreteValuationRing
