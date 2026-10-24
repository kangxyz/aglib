/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.PureDegreeP.FiniteDegree
public import Aglib.RingTheory.IntegralClosure.PurelyInseparable
public import Mathlib.RingTheory.IsAdjoinRoot
public import Mathlib.RingTheory.Nakayama
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Algebra.Subalgebra.IsSimpleOrder
public import Mathlib.Tactic.Ring

/-!
# Monogenicity of the original finite pure degree-p DVR extension

The finite-degree supplier precedes this leaf. Finiteness is used in Nakayama
on the original B. No power basis or monogenicity is an input to either public
branch theorem.
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial

namespace IsDiscreteValuationRing

section Generation

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsLocalRing A] [Module.Finite A B]

private theorem adjoin_eq_top_of_polynomial_remainders (z : B) (a : A)
    (ha : a ∈ maximalIdeal A)
    (hrem : ∀ b : B, ∃ q : A[X], ∃ c : B,
      b = aeval z q + algebraMap A B a * c) : Algebra.adjoin A {z} = ⊤ := by
  apply Algebra.toSubmodule_eq_top.mp
  apply top_unique
  apply Submodule.le_of_le_smul_of_le_jacobson_bot
    (Module.finite_def.mp inferInstance) (maximalIdeal_le_jacobson ⊥)
  intro b _
  obtain ⟨q, c, hbc⟩ := hrem b
  refine Submodule.mem_sup.mpr ⟨aeval z q, ?_, algebraMap A B a * c, ?_, hbc.symm⟩
  · change aeval z q ∈ Algebra.adjoin A {z}
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨q, rfl⟩
  · simpa only [Algebra.smul_def] using
      (Submodule.smul_mem_smul ha (Submodule.mem_top) :
        a • c ∈ maximalIdeal A • (⊤ : Submodule A B))

end Generation

section ResidueExpansion

variable {A B : Type*} [CommRing A] [IsLocalRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- Repeated division by the actual target uniformizer lifts residue coefficients
from A. This retains the original evaluation map at every finite stage. -/
theorem exists_polynomial_remainder_of_residue_surjective
    {τ : B} (hτ : Irreducible τ)
    (hres : Function.Surjective (algebraMap (ResidueField A) (ResidueField B)))
    (n : ℕ) (b : B) :
    ∃ q : A[X], ∃ c : B, b = aeval τ q + τ ^ n * c := by
  induction n generalizing b with
  | zero => exact ⟨0, b, by simp⟩
  | succ n ih =>
    obtain ⟨abar, habar⟩ := hres (residue B b)
    obtain ⟨a, ha⟩ := residue_surjective (R := A) abar
    have hzero : residue B (b - algebraMap A B a) = 0 := by
      rw [map_sub, ← ResidueField.algebraMap_residue, ha, habar, sub_self]
    have hmem : b - algebraMap A B a ∈ maximalIdeal B :=
      (residue_eq_zero_iff (R := B) _).mp hzero
    rw [hτ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    obtain ⟨q, d, hd⟩ := ih c
    refine ⟨C a + X * q, d, ?_⟩
    calc
      b = algebraMap A B a + τ * c := (sub_eq_iff_eq_add.mp hc).trans (add_comm _ _)
      _ = algebraMap A B a + τ * (aeval τ q + τ ^ n * d) := by rw [hd]
      _ = aeval τ (C a + X * q) + τ ^ (n + 1) * d := by
        rw [map_add, aeval_C, map_mul, aeval_X, pow_succ]
        ring

end ResidueExpansion

section Presentation

variable {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing B] [IsDomain B] [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B]

private theorem exists_presentation_of_adjoin
    {p : ℕ} (hp : p ≠ 0) (hdegree : Module.finrank A B = p)
    (z : B) (a : A) (hpow : algebraMap A B a = z ^ p)
    (hgen : Algebra.adjoin A {z} = ⊤) :
    ∃ h : IsAdjoinRootMonic B ((X : A[X]) ^ p - C a),
      h.root = z ∧ h.map = aeval z := by
  have hz : IsIntegral A z := Algebra.IsIntegral.isIntegral z
  let h₀ := IsAdjoinRootMonic.mkOfAdjoinEqTop hz hgen
  have hdegree' : (minpoly A z).natDegree = p := h₀.finrank.symm.trans hdegree
  have hzero : aeval z ((X : A[X]) ^ p - C a) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, ← hpow, sub_self]
  have hdiv : minpoly A z ∣ (X : A[X]) ^ p - C a :=
    (minpoly.isIntegrallyClosed_dvd_iff hz _).mp hzero
  have heq : (X : A[X]) ^ p - C a = minpoly A z :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hz)
      (Polynomial.monic_X_pow_sub_C a hp) hdiv
      (by simpa only [Polynomial.natDegree_sub_C, Polynomial.natDegree_X_pow, hdegree']
        using (le_refl p))
  let h : IsAdjoinRootMonic B ((X : A[X]) ^ p - C a) :=
    { map := aeval z
      map_surjective := h₀.map_surjective
      ker_map := by rw [heq]; exact h₀.ker_map
      monic := Polynomial.monic_X_pow_sub_C a hp }
  refine ⟨h, ?_, rfl⟩
  change aeval z X = z
  exact aeval_X z

end Presentation

section DVRBranches

variable (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra B L] [IsFractionRing B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  [FiniteDimensional K L] [IsPurelyInseparable K L]
  (p : ℕ) [Fact p.Prime] [CharP K p]

/-- In residue degree one, every actual B-uniformizer gives the required
presentation of the original B. Nakayama derives generation from finiteness. -/
theorem exists_presentation_of_residue_finrank_one
    (hdegree : Module.finrank K L = p)
    (hf : Module.finrank (ResidueField A) (ResidueField B) = 1)
    {τ : B} (hτ : Irreducible τ) :
    ∃ a : A, ∃ h : IsAdjoinRootMonic B ((X : A[X]) ^ p - C a),
      algebraMap A B a = τ ^ p ∧ h.root = τ ∧ h.map = aeval τ := by
  have hp : p.Prime := Fact.out
  let : IsLocalHom (algebraMap A B) := inferInstance
  have hres : Function.Surjective (algebraMap (ResidueField A) (ResidueField B)) := by
    intro x
    obtain ⟨c, hc⟩ :=
      (finrank_eq_one_iff_of_nonzero' (1 : ResidueField B) one_ne_zero).mp hf x
    exact ⟨c, by simpa only [Algebra.smul_def, mul_one] using hc⟩
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_pow_of_finite_pure_degree A B K L p hdegree τ
  have ham : a ∈ maximalIdeal A := by
    rw [Ideal.over_def (maximalIdeal B) (maximalIdeal A)]
    change algebraMap A B a ∈ maximalIdeal B
    rw [ha, ← Nat.sub_add_cancel hp.pos, pow_succ]
    exact (maximalIdeal B).mul_mem_left _
      (by rw [hτ.maximalIdeal_eq]; exact Ideal.subset_span (by simp))
  have hgen : Algebra.adjoin A {τ} = ⊤ := by
    apply adjoin_eq_top_of_polynomial_remainders τ a ham
    intro b
    obtain ⟨q, c, hbc⟩ := exists_polynomial_remainder_of_residue_surjective hτ hres p b
    exact ⟨q, c, by rw [ha]; exact hbc⟩
  have hrank : Module.finrank A B = p :=
    (IsFractionRing.finrank_eq A K B L).symm.trans hdegree
  obtain ⟨h, hroot, hmap⟩ := exists_presentation_of_adjoin hp.ne_zero hrank τ a ha hgen
  exact ⟨a, h, ha, hroot, hmap⟩

/-- In ramification index one, a residue class outside the original base
field generates by prime degree. Its original lift then generates B by Nakayama. -/
theorem exists_presentation_of_residue_not_mem_range
    (hdegree : Module.finrank K L = p)
    (hf : Module.finrank (ResidueField A) (ResidueField B) = p)
    (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    (z : B) (hz : residue B z ∉ Set.range (algebraMap (ResidueField A) (ResidueField B))) :
    ∃ a : A, ∃ h : IsAdjoinRootMonic B ((X : A[X]) ^ p - C a),
      algebraMap A B a = z ^ p ∧ h.root = z ∧ h.map = aeval z := by
  have hp : p.Prime := Fact.out
  let : IsLocalHom (algebraMap A B) := inferInstance
  have hfprime : (Module.finrank (ResidueField A) (ResidueField B)).Prime := by rwa [hf]
  have hgenResidue : Algebra.adjoin (ResidueField A) {residue B z} = ⊤ := by
    rcases (Subalgebra.isSimpleOrder_of_finrank_prime
      (ResidueField A) (ResidueField B) hfprime).eq_bot_or_eq_top
        (Algebra.adjoin (ResidueField A) {residue B z}) with hbot | htop
    · have hmem := Algebra.self_mem_adjoin_singleton (ResidueField A) (residue B z)
      rw [hbot, Algebra.mem_bot] at hmem
      exact (hz hmem).elim
    · exact htop
  obtain ⟨π, hπ⟩ := exists_irreducible A
  have hπm : π ∈ maximalIdeal A := by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.subset_span (by simp)
  have hgen : Algebra.adjoin A {z} = ⊤ := by
    apply adjoin_eq_top_of_polynomial_remainders z π hπm
    intro b
    have hmem : residue B b ∈ Set.range (aeval (residue B z) :
        (ResidueField A)[X] → ResidueField B) := by
      rw [← AlgHom.coe_range, ← Algebra.adjoin_singleton_eq_range_aeval, hgenResidue]
      trivial
    obtain ⟨qbar, hqbar⟩ := hmem
    obtain ⟨q, hq⟩ := Polynomial.map_surjective (residue A)
      (residue_surjective (R := A)) qbar
    have hcomm : (residue B).comp (algebraMap A B) =
        (algebraMap (ResidueField A) (ResidueField B)).comp (residue A) := by
      ext a
      exact (ResidueField.algebraMap_residue a).symm
    have heval : residue B (aeval z q) = aeval (residue B z) (q.map (residue A)) :=
      Polynomial.map_aeval_eq_aeval_map hcomm.symm q z
    have hzero : residue B (b - aeval z q) = 0 := by
      rw [map_sub, heval, hq, hqbar, sub_self]
    have hdiff : b - aeval z q ∈ maximalIdeal B :=
      (residue_eq_zero_iff (R := B) _).mp hzero
    have hmπ : maximalIdeal B = Ideal.span {algebraMap A B π} := by
      rw [← hm, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
    rw [hmπ, Ideal.mem_span_singleton] at hdiff
    obtain ⟨c, hc⟩ := hdiff
    exact ⟨q, c, (sub_eq_iff_eq_add.mp hc).trans (add_comm _ _)⟩
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_pow_of_finite_pure_degree A B K L p hdegree z
  have hrank : Module.finrank A B = p :=
    (IsFractionRing.finrank_eq A K B L).symm.trans hdegree
  obtain ⟨h, hroot, hmap⟩ := exists_presentation_of_adjoin hp.ne_zero hrank z a ha hgen
  exact ⟨a, h, ha, hroot, hmap⟩

/-- The residue pth-power equation is induced from the original normal ring,
not from a separability assertion about the residue fields. -/
theorem residue_pow_mem_range_of_finite_pure_degree
    (hdegree : Module.finrank K L = p) (x : ResidueField B) :
    x ^ p ∈ (algebraMap (ResidueField A) (ResidueField B)).range := by
  obtain ⟨b, rfl⟩ := residue_surjective (R := B) x
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_pow_of_finite_pure_degree A B K L p hdegree b
  refine ⟨residue A a, ?_⟩
  rw [ResidueField.algebraMap_residue, ha, map_pow]

/-- A finite original DVR extension of pure prime generic degree has one of
the two constructed monogenic presentations. No basis, generation, closed-fibre
identity, or defectless assertion is supplied to this theorem. -/
theorem exists_presentation_of_finite_pure_degree
    (hdegree : Module.finrank K L = p) :
    ∃ a : A, ∃ z : B, ∃ h : IsAdjoinRootMonic B ((X : A[X]) ^ p - C a),
      algebraMap A B a = z ^ p ∧ h.root = z ∧ h.map = aeval z ∧
        (Irreducible z ∨
          residue B z ∉ Set.range (algebraMap (ResidueField A) (ResidueField B))) := by
  classical
  have hp : p.Prime := Fact.out
  let : IsLocalHom (algebraMap A B) := inferInstance
  obtain ⟨π, hπ⟩ := exists_irreducible A
  obtain ⟨τ, hτ⟩ := exists_irreducible B
  have hπB : algebraMap A B π ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B)).mpr hπ.ne_zero
  obtain ⟨e, u, he⟩ := eq_unit_mul_pow_irreducible hπB hτ
  rcases uniformizerExponent_residue_cases A B K L hp hdegree hπ hτ u e he with hcase | hcase
  · obtain ⟨a, h, ha, hroot, hmap⟩ :=
      exists_presentation_of_residue_finrank_one A B K L p hdegree hcase.2 hτ
    exact ⟨a, τ, h, ha, hroot, hmap, Or.inl hτ⟩
  · have hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
      rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, he, hcase.1,
        pow_one, Ideal.span_singleton_mul_left_unit u.isUnit, ← hτ.maximalIdeal_eq]
    have hex : ∃ x : ResidueField B,
        x ∉ Set.range (algebraMap (ResidueField A) (ResidueField B)) := by
      by_contra h
      have hall : ∀ x : ResidueField B,
          x ∈ Set.range (algebraMap (ResidueField A) (ResidueField B)) := by
        simpa only [not_exists, not_not] using h
      have hbot : (⊥ : Subalgebra (ResidueField A) (ResidueField B)) = ⊤ := by
        apply top_unique
        intro x _
        exact Algebra.mem_bot.mpr (hall x)
      have hone : Module.finrank (ResidueField A) (ResidueField B) = 1 :=
        Subalgebra.bot_eq_top_iff_finrank_eq_one.mp hbot
      exact hp.ne_one (hcase.2.symm.trans hone)
    obtain ⟨x, hx⟩ := hex
    obtain ⟨z, hz⟩ := residue_surjective (R := B) x
    have hz' : residue B z ∉ Set.range (algebraMap (ResidueField A) (ResidueField B)) := by
      simpa only [hz] using hx
    obtain ⟨a, h, ha, hroot, hmap⟩ :=
      exists_presentation_of_residue_not_mem_range A B K L p hdegree hcase.2 hm z hz'
    exact ⟨a, z, h, ha, hroot, hmap, Or.inr hz'⟩

end DVRBranches

end IsDiscreteValuationRing

namespace integralClosure

variable (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsPurelyInseparable K L]
  [Module.Finite A (integralClosure A L)]
  (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The actual finite integral closure receives its actual root presentation.
Its DVR and fraction-field structures are derived from the original normalization. -/
theorem exists_presentation_of_finite_pure_degree
    (hdegree : Module.finrank K L = p) :
    ∃ a : A, ∃ z : integralClosure A L,
      ∃ h : IsAdjoinRootMonic (integralClosure A L) ((X : A[X]) ^ p - C a),
        algebraMap A (integralClosure A L) a = z ^ p ∧
          h.root = z ∧ h.map = aeval z := by
  let : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  let : Module.IsTorsionFree A (integralClosure A L) := IsIntegralClosure.isTorsionFree A L
  let : IsFractionRing (integralClosure A L) L := isFractionRing_of_finite_extension K L
  let : IsDiscreteValuationRing (integralClosure A L) :=
    isDiscreteValuationRing_of_isPurelyInseparable A K L
  obtain ⟨a, z, h, ha, hroot, hmap, _⟩ :=
    IsDiscreteValuationRing.exists_presentation_of_finite_pure_degree
      A (integralClosure A L) K L p hdegree
  exact ⟨a, z, h, ha, hroot, hmap⟩

end integralClosure
