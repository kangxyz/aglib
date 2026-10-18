/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Data.Nat.Prime.Pow

/-!
# An actual normal prime subfield inside a finite p-group extension

In a finite Galois ambient extension with p-group automorphisms, every
nontrivial intermediate field contains a normal degree-p subfield. Native
Sylow subgroup interpolation supplies an index-p overgroup of the actual
fixing subgroup. Its fixed field is then restricted into the original
intermediate field, strictly decreasing the remaining extension degree.
-/

@[expose] public noncomputable section

namespace IntermediateField

private theorem exists_normal_prime_index_overgroup {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G) (H : Subgroup G) (hH : H ≠ ⊤) :
    ∃ J : Subgroup G, H ≤ J ∧ J.Normal ∧ J.index = p := by
  have hp : p.Prime := Fact.out
  obtain ⟨N, hN⟩ := hG.exists_card_eq
  obtain ⟨m, hm⟩ := (hG.to_subgroup H).exists_card_eq
  have hcard : Nat.card H < Nat.card G :=
    lt_of_not_ge fun h => hH (H.eq_top_of_le_card h)
  have hmN : m < N := (Nat.pow_lt_pow_iff_right hp.one_lt).mp (by rwa [← hm, ← hN])
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le m) hmN
  have hdvd : p ^ (N - 1) ∣ Nat.card G := by
    rw [hN]
    exact pow_dvd_pow p (Nat.sub_le N 1)
  obtain ⟨J, hJcard, hHJ⟩ := Sylow.exists_subgroup_card_pow_prime_le p hdvd H hm
    (Nat.le_sub_one_of_lt hmN)
  have hprod : p ^ (N - 1) * J.index = p ^ (N - 1) * p := by
    calc
      _ = Nat.card J * J.index := by rw [hJcard]
      _ = Nat.card G := J.card_mul_index
      _ = p ^ (N - 1) * p := by rw [hN, ← pow_succ, Nat.sub_add_cancel hNpos]
  have hindex : J.index = p := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) hprod
  refine ⟨J, hHJ, ?_, hindex⟩
  apply Subgroup.normal_of_index_eq_minFac_card
  rw [hindex, hN, hp.pow_minFac (Nat.ne_of_gt hNpos)]

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
  [FiniteDimensional k Ω] [IsGalois k Ω]

/-- The normal index-p subgroup contains the actual fixing subgroup, so its
actual fixed field lies inside the given intermediate field. -/
theorem exists_normal_prime_fixedField (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (Ω ≃ₐ[k] Ω)) (E : IntermediateField k Ω) (hE : E ≠ ⊥) :
    ∃ J : Subgroup (Ω ≃ₐ[k] Ω), E.fixingSubgroup ≤ J ∧ J.Normal ∧ J.index = p ∧
      fixedField J ≤ E ∧ Module.finrank k (fixedField J) = p ∧ Normal k (fixedField J) := by
  have hH : E.fixingSubgroup ≠ ⊤ := by
    intro h
    apply hE
    rw [← IsGalois.fixedField_fixingSubgroup E, h, IsGalois.fixedField_top]
  obtain ⟨J, hHJ, hJnormal, hJindex⟩ :=
    exists_normal_prime_index_overgroup p hG E.fixingSubgroup hH
  let : J.Normal := hJnormal
  have hJE : fixedField J ≤ E := by
    rw [← IsGalois.fixedField_fixingSubgroup E]
    exact fixedField_le hHJ
  refine ⟨J, hHJ, hJnormal, hJindex, hJE, ?_, inferInstance⟩
  rw [finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedField, hJindex]

/-- Restricting the actual fixed field produces a normal prime-degree
subfield of the original field, with strictly smaller remaining degree. -/
theorem exists_normal_prime_subfield_of_isPGroup (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (Ω ≃ₐ[k] Ω)) (E : IntermediateField k Ω) (hE : E ≠ ⊥) :
    ∃ L : IntermediateField k E, Normal k L ∧ Module.finrank k L = p ∧
      Module.finrank L E < Module.finrank k E := by
  obtain ⟨J, _, _, _, hJE, hdegree, hnormal⟩ := exists_normal_prime_fixedField p hG E hE
  let L : IntermediateField k E := restrict hJE
  let ε : fixedField J ≃ₐ[k] L := restrictAlgEquiv hJE
  let : Normal k (fixedField J) := hnormal
  have hLnormal : Normal k L := Normal.of_algEquiv ε
  have hLdegree : Module.finrank k L = p := ε.toLinearEquiv.finrank_eq.symm.trans hdegree
  refine ⟨L, hLnormal, hLdegree, ?_⟩
  rw [← Module.finrank_mul_finrank k L E, hLdegree]
  exact lt_mul_of_one_lt_left Module.finrank_pos (Fact.out : p.Prime).one_lt

end IntermediateField
