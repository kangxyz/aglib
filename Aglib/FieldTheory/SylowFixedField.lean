/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.SplittingField.IsSplittingField
public import Mathlib.GroupTheory.Sylow

/-!
# Small polynomials over a finite Sylow fixed field

In a finite Galois extension `M/k`, the fixed field of a Sylow `p`-subgroup
has degree prime to `p` over `k`. A polynomial over `k` of degree below `p`
which splits in the specified field `M` already splits in that fixed field.

The proof uses minimal-polynomial degrees in the finite prime-power extension
above the fixed field. Zero and constant polynomials are included in the
splitting statement. No infinite special-field extension is constructed, and
no splitting claim is made for polynomials not known to split in `M`.
-/

@[expose] public noncomputable section

namespace IntermediateField

open Polynomial

variable {k M : Type*} [Field k] [Field M] [Algebra k M]

/-- A root of a nonzero small-degree polynomial cannot have nontrivial degree
inside a prime-power extension. The polynomial may have constant coefficients
from the original base field. -/
theorem mem_of_small_root_of_finrank_prime_pow (S : IntermediateField k M)
    [FiniteDimensional S M] (p r : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank S M = p ^ r)
    (q : k[X]) (hq : q ≠ 0) (hqd : q.natDegree < p)
    (x : M) (hx : aeval x q = 0) : x ∈ S := by
  have hxint : IsIntegral S x := IsIntegral.of_finite S x
  have hmin : minpoly S x ∣ q.map (algebraMap k S) :=
    minpoly.dvd S x (by rwa [aeval_map_algebraMap])
  have hsmall : (minpoly S x).natDegree < p := by
    have hle := natDegree_le_of_dvd hmin (Polynomial.map_ne_zero hq)
    rw [natDegree_map] at hle
    exact hle.trans_lt hqd
  have hpos : 0 < (minpoly S x).natDegree := minpoly.natDegree_pos hxint
  have hcop : p.Coprime (minpoly S x).natDegree :=
    hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hpos hsmall)
  have hdvd : (minpoly S x).natDegree ∣ p ^ r := by
    rw [← hdegree]
    exact minpoly.degree_dvd hxint
  have hdegone : (minpoly S x).natDegree = 1 :=
    Nat.eq_one_of_dvd_coprimes (hcop.pow_left r) hdvd dvd_rfl
  obtain ⟨a, ha⟩ := minpoly.natDegree_eq_one_iff.mp hdegone
  rw [← ha]
  exact a.property

/-- Small polynomials that split in a finite prime-power overfield already
split in the given intermediate field. The zero polynomial is handled explicitly. -/
theorem splits_of_small_degree_of_finrank_prime_pow (S : IntermediateField k M)
    [FiniteDimensional S M] (p r : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank S M = p ^ r)
    (q : k[X]) (hqd : q.natDegree < p)
    (hq : (q.map (algebraMap k M)).Splits) :
    (q.map (algebraMap k S)).Splits := by
  by_cases hq0 : q = 0
  · simp only [hq0, Polynomial.map_zero, Splits.zero]
  · apply splits_of_splits hq
    intro x hx
    exact mem_of_small_root_of_finrank_prime_pow S p r hp hdegree q hq0 hqd x
      (aeval_eq_zero_of_mem_rootSet hx)

variable [FiniteDimensional k M] (p : ℕ) [Fact p.Prime]

/-- The degree above a finite Sylow fixed field is an actual power of the prime. -/
theorem finrank_over_sylow_fixedField
    (H : Sylow p (M ≃ₐ[k] M)) :
    ∃ r : ℕ, Module.finrank (fixedField (H : Subgroup (M ≃ₐ[k] M))) M = p ^ r := by
  obtain ⟨r, hr⟩ := H.isPGroup'.exists_card_eq
  exact ⟨r, (finrank_fixedField_eq_card (H : Subgroup (M ≃ₐ[k] M))).trans hr⟩

/-- Every specified polynomial of degree below `p` that splits in the finite
extension also splits over its Sylow fixed field. -/
theorem splits_over_sylow_fixedField_of_small_degree
    (H : Sylow p (M ≃ₐ[k] M)) (q : k[X]) (hqd : q.natDegree < p)
    (hq : (q.map (algebraMap k M)).Splits) :
    (q.map (algebraMap k (fixedField (H : Subgroup (M ≃ₐ[k] M))))).Splits := by
  obtain ⟨r, hr⟩ := finrank_over_sylow_fixedField p H
  exact splits_of_small_degree_of_finrank_prime_pow _ p r Fact.out hr q hqd hq

/-- For a finite Galois extension, the actual base degree of a Sylow fixed field
is prime to `p`. -/
theorem coprime_finrank_sylow_fixedField [IsGalois k M]
    (H : Sylow p (M ≃ₐ[k] M)) :
    p.Coprime (Module.finrank k (fixedField (H : Subgroup (M ≃ₐ[k] M)))) := by
  rw [finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedField]
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr H.not_dvd_index

/-- A finite family already split in the chosen finite Galois field has a
simultaneous finite prime-to-`p` splitting subfield when each degree is below `p`.
The conclusion concerns only the supplied polynomial family. -/
theorem exists_coprime_splitting_intermediateField [IsGalois k M]
    (s : Finset k[X]) (hsmall : ∀ q ∈ s, q.natDegree < p)
    (hsplit : ∀ q ∈ s, (q.map (algebraMap k M)).Splits) :
    ∃ S : IntermediateField k M, FiniteDimensional k S ∧
      p.Coprime (Module.finrank k S) ∧
      ∀ q ∈ s, (q.map (algebraMap k S)).Splits := by
  let H : Sylow p (M ≃ₐ[k] M) := Classical.arbitrary _
  refine ⟨fixedField (H : Subgroup (M ≃ₐ[k] M)), inferInstance,
    coprime_finrank_sylow_fixedField p H, ?_⟩
  intro q hq
  exact splits_over_sylow_fixedField_of_small_degree p H q (hsmall q hq) (hsplit q hq)

end IntermediateField
