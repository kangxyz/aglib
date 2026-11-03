/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.DimensionOne
public import Aglib.RingTheory.DiscreteValuationRing.PureDegreeP.Monogenic
public import Aglib.RingTheory.IntegralClosure.Localization
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# The actual height-one normalization in a pure prime-degree field extension

Every normalization is the literal integralClosure in the original L.
The localized closure is first the localization at the
base complement, then the localization at the unique prime above it. Module
finiteness is transported from the original finite normalization. No
defectlessness, residue separability, or chosen power basis is an input.
-/

@[expose] public noncomputable section

open Polynomial
open scoped nonZeroDivisors

namespace integralClosure

section PureDegree

variable (A K L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsPurelyInseparable K L]
  (p : ℕ) [Fact p.Prime] [CharP K p]

omit [IsDomain A] in
/-- Original normality puts each actual pth power in the original A. -/
theorem pow_mem_base_of_pure_degree
    (hdegree : Module.finrank K L = p) (b : integralClosure A L) :
    ∃ a : A, algebraMap A (integralClosure A L) a = b ^ p := by
  obtain ⟨k, hk⟩ :=
    IsPurelyInseparable.pow_mem_range_of_finrank_eq_prime K L p hdegree (b : L)
  have hK : (b : L) ^ p ∈ (algebraMap K L).range := ⟨k, hk⟩
  obtain ⟨a, ha⟩ :=
    (mem_iff_pow_mem_range A K L (b : L) p (Fact.out : p.Prime).pos hK).mp b.property
  refine ⟨a, ?_⟩
  apply Subtype.ext
  exact ha

omit [IsDomain A] in
/-- Two primes above the same original prime coincide by actual pth powers. -/
theorem prime_eq_of_pure_degree
    (hdegree : Module.finrank K L = p) (q : Ideal A)
    (Q Q' : Ideal (integralClosure A L)) [Q.IsPrime] [Q'.IsPrime]
    [Q.LiesOver q] [Q'.LiesOver q] : Q = Q' := by
  apply Ideal.ext
  intro b
  obtain ⟨a, ha⟩ := pow_mem_base_of_pure_degree A K L p hdegree b
  calc
    b ∈ Q ↔ b ^ p ∈ Q :=
      ((inferInstance : Q.IsPrime).pow_mem_iff_mem p (Fact.out : p.Prime).pos).symm
    _ ↔ a ∈ q := by rw [← ha]; exact (Ideal.mem_of_liesOver Q q a).symm
    _ ↔ b ^ p ∈ Q' := by rw [← ha]; exact Ideal.mem_of_liesOver Q' q a
    _ ↔ b ∈ Q' :=
      (inferInstance : Q'.IsPrime).pow_mem_iff_mem p (Fact.out : p.Prime).pos

/-- Lying over and the pth-power argument give the unique original prime. -/
theorem existsUnique_prime_of_pure_degree
    (hdegree : Module.finrank K L = p) (q : Ideal A) [q.IsPrime] :
    ∃! Q : Ideal (integralClosure A L), Q.IsPrime ∧ Q.LiesOver q := by
  let : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  let : Module.IsTorsionFree A (integralClosure A L) :=
    IsIntegralClosure.isTorsionFree A L
  let : Algebra.IsIntegral A (integralClosure A L) :=
    IsIntegralClosure.isIntegral_algebra A L
  obtain ⟨Q⟩ := (inferInstance : Nonempty (q.primesOver (integralClosure A L)))
  refine ⟨Q.1, Q.2, ?_⟩
  intro Q' hQ'
  let : Q'.IsPrime := hQ'.1
  let : Q'.LiesOver q := hQ'.2
  exact prime_eq_of_pure_degree A K L p hdegree q Q' Q.1

variable (D : Type*) [CommRing D] [Algebra A D]
  [Algebra D L] [IsScalarTower A D L]
  (q : Ideal A) [q.IsPrime] [IsLocalization q.primeCompl D]

omit [IsDomain A] in
/-- The literal localized normalization is the actual localization of B at
the unique prime above q. Its algebra map is the ambient-element inclusion. -/
theorem scalarExtension_isLocalization_atPrime_of_pure_degree
    (hdegree : Module.finrank K L = p)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver q] :
    letI := scalarExtensionAlgebra A D L
    IsLocalization.AtPrime (integralClosure D L) Q := by
  let := scalarExtensionAlgebra A D L
  let := scalarExtension_isScalarTower_base A D L
  let := scalarExtension_isScalarTower_ambient A D L
  let := scalarExtension_isLocalization A D L q.primeCompl
  let U := Algebra.algebraMapSubmonoid (integralClosure A L) q.primeCompl
  apply IsLocalization.of_le_of_exists_dvd U Q.primeCompl
  · rintro _ ⟨a, ha, rfl⟩
    exact fun h => ha ((Ideal.mem_of_liesOver Q q a).mpr h)
  · intro b hb
    obtain ⟨a, ha⟩ := pow_mem_base_of_pure_degree A K L p hdegree b
    have haq : a ∉ q := by
      intro h
      have hpow : b ^ p ∈ Q := by
        rw [← ha]
        exact (Ideal.mem_of_liesOver Q q a).mp h
      exact hb ((inferInstance : Q.IsPrime).mem_of_pow_mem p hpow)
    refine ⟨b ^ p, ?_, ?_⟩
    · exact ⟨a, haq, ha⟩
    · refine ⟨b ^ (p - 1), ?_⟩
      rw [← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le]

end PureDegree

section HeightOne

variable (A D : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [IsIntegrallyClosed A] [CommRing D] [IsDomain D] [Algebra A D]
  (q : Ideal A) [q.IsPrime] [IsLocalization q.primeCompl D]

/-- The original height-one localization of a normal Noetherian domain is a DVR. -/
theorem isDiscreteValuationRing_of_height_one (hq : q.height = 1) :
    IsDiscreteValuationRing D := by
  let : IsDomain D :=
    IsLocalization.isDomain_of_le_nonZeroDivisors D q.primeCompl_le_nonZeroDivisors
  let : IsLocalRing D := IsLocalization.AtPrime.isLocalRing D q
  let : IsNoetherianRing D := IsLocalization.isNoetherianRing q.primeCompl D inferInstance
  let : IsIntegrallyClosed D :=
    isIntegrallyClosed_of_isLocalization D q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hqne : q ≠ ⊥ := by
    intro h
    have hz : q.height = 0 := Ideal.height_eq_zero_iff_eq_bot.mpr h
    rw [hq] at hz
    exact one_ne_zero hz
  have hdim : ringKrullDim D = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q D, hq]
    rfl
  exact IsDiscreteValuationRing.of_isIntegrallyClosed_of_dimLE_one D hdim.le
    (IsLocalization.AtPrime.not_isField A hqne D)

variable (K L : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  [Algebra D K] [IsScalarTower A D K]
  [Field L] [Algebra K L] [Algebra A L] [Algebra D L]
  [IsScalarTower A K L] [IsScalarTower D K L] [IsScalarTower A D L]
  [FiniteDimensional K L] [IsPurelyInseparable K L]
  [Module.Finite A (integralClosure A L)]
  (p : ℕ) [Fact p.Prime] [CharP K p]

omit [IsDomain D] [IsScalarTower A K L] in
/-- Original global finiteness supplies local finiteness; the original local
normalization therefore has the passed actual pure-degree-p presentation. -/
theorem exists_presentation_at_height_one_of_pure_degree
    (hq : q.height = 1) (hdegree : Module.finrank K L = p) :
    ∃ a : D, ∃ z : integralClosure D L,
      ∃ h : IsAdjoinRootMonic (integralClosure D L) ((X : D[X]) ^ p - C a),
        algebraMap D (integralClosure D L) a = z ^ p ∧
          h.root = z ∧ h.map = aeval z := by
  let : IsDomain D :=
    IsLocalization.isDomain_of_le_nonZeroDivisors D q.primeCompl_le_nonZeroDivisors
  let : IsDiscreteValuationRing D := isDiscreteValuationRing_of_height_one A D q hq
  let : IsFractionRing D K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl D K
  let : IsLocalizedModule q.primeCompl (scalarExtensionHom A D L).toLinearMap :=
    scalarExtensionHom_isLocalizedModule A D L q.primeCompl
  let : Module.Finite D (integralClosure D L) :=
    Module.Finite.of_isLocalizedModule q.primeCompl (scalarExtensionHom A D L).toLinearMap
  exact exists_presentation_of_finite_pure_degree D K L p hdegree

end HeightOne

end integralClosure
