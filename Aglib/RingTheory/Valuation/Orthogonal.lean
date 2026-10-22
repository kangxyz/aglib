/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Valuation.Sequences
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Tactic.FieldSimp

/-!
# Finite orthogonal spans over complete valued coefficient subfields.
-/

@[expose] public noncomputable section

open scoped BigOperators
open WithZero

namespace Valuation

variable {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰) (E : Subfield K)

/-- The coordinatewise formulation includes the empty family without a nonempty supremum.
Together with the valuation inequality for sums it is exactly the maximum formula. -/
def IsOrthogonal {ι : Type*} [Fintype ι] (b : ι → K) : Prop :=
  ∀ c : ι → E, ∀ i, v ((c i : K) * b i) ≤ v (∑ j, (c j : K) * b j)

/-- Orthogonality is the exact finite maximum formula, including the empty family. -/
theorem IsOrthogonal.map_sum_eq_sup {ι : Type*} [Fintype ι] {b : ι → K}
    (hb : v.IsOrthogonal E b) (c : ι → E) :
    v (∑ i, (c i : K) * b i) = Finset.univ.sup (fun i => v ((c i : K) * b i)) := by
  classical
  apply le_antisymm
  · exact v.map_sum_le (fun i hi => Finset.le_sup (f := fun j => v ((c j : K) * b j)) hi)
  · exact Finset.sup_le (fun i hi => hb c i)

/-- Completeness of a finite orthogonal span is proved coordinate by coordinate. -/
theorem IsOrthogonal.isSeqCompleteSet_span {ι : Type*} [Fintype ι]
    {b : ι → K} (hb : v.IsOrthogonal E b) (hli : LinearIndependent E b)
    (hE : v.IsSeqCompleteSet (E : Set K)) :
    v.IsSeqCompleteSet (Submodule.span E (Set.range b) : Set K) := by
  classical
  intro s hs hc
  let B := Module.Basis.span hli
  let c (n : ℕ) (i : ι) : E := B.repr ⟨s n, hs n⟩ i
  have hsum (n : ℕ) : ∑ i, (c n i : K) * b i = s n := by
    simpa only [c, B, Submodule.coe_sum, Submodule.coe_smul,
      Module.Basis.coe_span_apply, Subfield.smul_def, smul_eq_mul] using
      congrArg Subtype.val (B.sum_repr ⟨s n, hs n⟩)
  have hb0 (i : ι) : v (b i) ≠ 0 := by simpa using hli.ne_zero i
  have hcauchy (i : ι) : v.SeqCauchy (fun n => (c n i : K)) := by
    intro γ hγ
    obtain ⟨N, hN⟩ := hc (γ * v (b i)) (mul_ne_zero hγ (hb0 i))
    refine ⟨N, fun m hm n hn => ?_⟩
    have horth := hb (fun j => c m j - c n j) i
    have hsumsub : (∑ j, ((c m j - c n j : E) : K) * b j) = s m - s n := by
      simp only [Subfield.coe_sub, sub_mul, Finset.sum_sub_distrib, hsum]
    rw [hsumsub, Subfield.coe_sub, map_mul] at horth
    exact (mul_lt_mul_iff_left₀ (pos_iff_ne_zero.mpr (hb0 i))).mp
      (horth.trans_lt (hN m hm n hn))
  have hlimits : ∀ i, ∃ x ∈ E, v.SeqTendsto (fun n => (c n i : K)) x :=
    fun i => hE _ (fun n => (c n i).property) (hcauchy i)
  choose a ha hconv using hlimits
  let d (i : ι) : E := ⟨a i, ha i⟩
  refine ⟨∑ i, a i * b i, ?_, ?_⟩
  · exact Submodule.sum_mem _ (fun i hi =>
      (Submodule.span E (Set.range b)).smul_mem (d i)
        (Submodule.subset_span (Set.mem_range_self i)))
  intro γ hγ
  have hterm (i : ι) := Valuation.SeqTendsto.mul_const v (hconv i) (b i) γ hγ
  choose N hN using hterm
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  rw [← hsum n, ← Finset.sum_sub_distrib]
  exact v.map_sum_lt hγ (fun i hi => hN i n
    ((Finset.le_sup (f := N) hi).trans hn))

/-- A complete subspace of a discretely valued field admits best approximations.
No compactness, residue-field finiteness, or spherical completeness is used. -/
theorem exists_bestApproximation (U : Submodule E K)
    (hU : v.IsSeqCompleteSet (U : Set K)) {x : K} (hx : x ∉ U) :
    ∃ u₀ ∈ U, ∀ u ∈ U, v (x - u₀) ≤ v (x - u) := by
  classical
  have hne (u : K) (hu : u ∈ U) : v (x - u) ≠ 0 := by
    have hxu : x ≠ u := by
      intro h
      apply hx
      rw [h]
      exact hu
    simpa using sub_ne_zero.mpr hxu
  let S : Set ℤ := {z | ∃ u ∈ U, WithZero.log (v (x - u)) = z}
  have hS : S.Nonempty := ⟨WithZero.log (v x), 0, U.zero_mem, by simp⟩
  have hbounded : BddBelow S := by
    by_contra hbad
    have hsmall (n : ℕ) : ∃ u ∈ U, v (x - u) < exp (-(n : ℤ)) := by
      obtain ⟨z, ⟨u, hu, huz⟩, hz⟩ := not_bddBelow_iff.mp hbad (-(n : ℤ))
      refine ⟨u, hu, ?_⟩
      rw [← exp_log (hne u hu), exp_lt_exp, huz]
      exact hz
    choose s hs hval using hsmall
    have hconv : v.SeqTendsto s x := by
      intro γ hγ
      obtain ⟨N, hN⟩ := exists_exp_neg_natCast_lt hγ
      refine ⟨N, fun n hn => ?_⟩
      rw [v.map_sub_swap]
      apply (hval n).trans_le
      exact (show exp (-(n : ℤ)) ≤ exp (-(N : ℤ)) by
        rw [exp_le_exp]; exact neg_le_neg (Int.ofNat_le.mpr hn)).trans hN.le
    obtain ⟨y, hy, hlim⟩ := hU s hs (Valuation.SeqTendsto.cauchy v hconv)
    exact hx ((Valuation.SeqTendsto.unique v hconv hlim).symm ▸ hy)
  obtain ⟨u₀, hu₀, heq⟩ := Int.csInf_mem hS hbounded
  refine ⟨u₀, hu₀, fun u hu => ?_⟩
  rw [← log_le_log (hne u₀ hu₀) (hne u hu), heq]
  exact csInf_le hbounded ⟨u, hu, rfl⟩

/-- Subtracting a best approximation makes the new direction orthogonal to the old span. -/
theorem bestApproximation_pair (U : Submodule E K) {x u₀ : K}
    (hu₀ : u₀ ∈ U) (hbest : ∀ u ∈ U, v (x - u₀) ≤ v (x - u))
    (c : E) {u : K} (hu : u ∈ U) :
    v ((c : K) * (x - u₀) + u) = max (v ((c : K) * (x - u₀))) (v u) := by
  by_cases hc : c = 0
  · simp [hc]
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc
  have hfirst : v ((c : K) * (x - u₀)) ≤ v ((c : K) * (x - u₀) + u) := by
    have h := hbest (u₀ - (c⁻¹ : E) • u) (U.sub_mem hu₀ (U.smul_mem _ hu))
    have hid : (c : K) * (x - (u₀ - (c⁻¹ : E) • u)) =
        (c : K) * (x - u₀) + u := by
      simp only [Subfield.smul_def, smul_eq_mul, Subfield.coe_inv]
      field_simp [hcK]
      ring
    have hh := mul_le_mul_of_nonneg_left h (zero_le : (0 : ℤᵐ⁰) ≤ v (c : K))
    simpa only [← map_mul, hid] using hh
  apply le_antisymm (v.map_add _ _)
  refine max_le hfirst ?_
  have hh := v.map_sub ((c : K) * (x - u₀) + u) ((c : K) * (x - u₀))
  simpa only [add_sub_cancel_left, max_eq_left hfirst] using hh

/-- Adding the best-approximation residual preserves finite orthogonality. -/
theorem IsOrthogonal.finCons {n : ℕ} {b : Fin n → K}
    (hb : v.IsOrthogonal E b) {x u₀ : K}
    (hu₀ : u₀ ∈ Submodule.span E (Set.range b))
    (hbest : ∀ u ∈ Submodule.span E (Set.range b), v (x - u₀) ≤ v (x - u)) :
    v.IsOrthogonal E (Fin.cons (x - u₀) b) := by
  intro c i
  have hsum : (∑ j : Fin (n + 1), (c j : K) * (Fin.cons (x - u₀) b : Fin (n + 1) → K) j) =
      (c 0 : K) * (x - u₀) + ∑ j : Fin n, (c j.succ : K) * b j := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  have hmem : (∑ j : Fin n, (c j.succ : K) * b j) ∈
      Submodule.span E (Set.range b) :=
    Submodule.sum_mem _ (fun j hj =>
      (Submodule.span E (Set.range b)).smul_mem (c j.succ)
        (Submodule.subset_span (Set.mem_range_self j)))
  rw [hsum, v.bestApproximation_pair E _ hu₀ hbest (c 0) hmem]
  refine Fin.cases ?_ (fun j => ?_) i
  · exact le_max_left _ _
  · exact (hb (fun j => c j.succ) j).trans (le_max_right _ _)

/-- Every finitely generated coefficient subspace has a finite orthogonal basis family. -/
theorem exists_orthogonal_span (hE : v.IsSeqCompleteSet (E : Set K))
    (W : Submodule E K) (hW : W.FG) :
    ∃ n : ℕ, ∃ b : Fin n → K, LinearIndependent E b ∧
      Submodule.span E (Set.range b) = W ∧ v.IsOrthogonal E b := by
  classical
  apply Submodule.fg_sup_span_induction
    (motive := fun W _ => ∃ n : ℕ, ∃ b : Fin n → K, LinearIndependent E b ∧
      Submodule.span E (Set.range b) = W ∧ v.IsOrthogonal E b) ?_ ?_ W hW
  · refine ⟨0, Fin.elim0, linearIndependent_empty_type, ?_, ?_⟩
    · simp
    · intro c i
      exact Fin.elim0 i
  intro U x hU ih
  obtain ⟨n, b, hli, hspan, hb⟩ := ih
  by_cases hx : x ∈ U
  · refine ⟨n, b, hli, ?_, hb⟩
    rw [hspan, sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem x U).mpr hx)]
  have hcomplete : v.IsSeqCompleteSet (U : Set K) := by
    rw [← hspan]
    exact Valuation.IsOrthogonal.isSeqCompleteSet_span v E hb hli hE
  obtain ⟨u₀, hu₀, hbest⟩ := v.exists_bestApproximation E U hcomplete hx
  have hnew : x - u₀ ∉ Submodule.span E (Set.range b) := by
    rw [hspan]
    intro h
    exact hx (by simpa only [sub_add_cancel] using U.add_mem h hu₀)
  refine ⟨n + 1, Fin.cons (x - u₀) b, hli.finCons hnew, ?_, ?_⟩
  · rw [Fin.range_cons, Submodule.span_insert, hspan, sup_comm]
    apply le_antisymm
    · apply sup_le le_sup_left
      apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      exact (U ⊔ E ∙ x).sub_mem
        ((show E ∙ x ≤ U ⊔ E ∙ x from le_sup_right)
          (Submodule.subset_span (Set.mem_singleton x)))
        ((show U ≤ U ⊔ E ∙ x from le_sup_left) hu₀)
    · apply sup_le le_sup_left
      apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      have h : x - u₀ + u₀ ∈ U ⊔ E ∙ (x - u₀) :=
        (U ⊔ E ∙ (x - u₀)).add_mem
          ((show E ∙ (x - u₀) ≤ U ⊔ E ∙ (x - u₀) from le_sup_right)
            (Submodule.subset_span (Set.mem_singleton _)))
          ((show U ≤ U ⊔ E ∙ (x - u₀) from le_sup_left) hu₀)
      simpa only [sub_add_cancel] using h
  · exact Valuation.IsOrthogonal.finCons v E hb (by simpa only [hspan] using hu₀)
      (by simpa only [hspan] using hbest)

/-- The result for finite-dimensional subspaces, over the literal Frobenius subfield. -/
theorem exists_frobenius_orthogonal_span (hK : v.IsSeqComplete)
    (p : ℕ) [ExpChar K p] (hp : 0 < p)
    (W : Submodule (frobenius K p).fieldRange K) [Module.Finite (frobenius K p).fieldRange W] :
    ∃ n : ℕ, ∃ b : Fin n → K,
      LinearIndependent (frobenius K p).fieldRange b ∧
      Submodule.span (frobenius K p).fieldRange (Set.range b) = W ∧
      v.IsOrthogonal (frobenius K p).fieldRange b := by
  exact v.exists_orthogonal_span (frobenius K p).fieldRange
    (v.isSeqCompleteSet_frobeniusFieldRange p hK hp) W (Module.Finite.iff_fg.mp inferInstance)

/-- Independent rescaling of basis vectors by coefficient-field elements preserves orthogonality. -/
theorem IsOrthogonal.mul {ι : Type*} [Fintype ι] {b : ι → K}
    (hb : v.IsOrthogonal E b) (a : ι → E) :
    v.IsOrthogonal E (fun i => (a i : K) * b i) := by
  intro c i
  simpa only [Subfield.coe_mul, mul_assoc] using hb (fun j => c j * a j) i

/-- Restricting to a subgroup of indices preserves orthogonality. -/
theorem IsOrthogonal.subtype {ι : Type*} [Fintype ι] {b : ι → K}
    (hb : v.IsOrthogonal E b) (P : ι → Prop) [DecidablePred P] :
    v.IsOrthogonal E (fun i : {i // P i} => b i) := by
  classical
  intro c i
  let d (j : ι) : E := if h : P j then c ⟨j, h⟩ else 0
  have hs : (∑ j : ι, (d j : K) * b j) =
      ∑ j : {j // P j}, (c j : K) * b j := by
    have hpos : (∑ j : {j // P j}, (d j : K) * b j) =
        ∑ j : {j // P j}, (c j : K) * b j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [d, dite_eq_left j.property]
    have hneg : (∑ j : {j // ¬P j}, (d j : K) * b j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [d, dite_eq_right j.property, Subfield.coe_zero, zero_mul]
    rw [← Fintype.sum_subtype_add_sum_subtype P (fun j => (d j : K) * b j),
      hpos, hneg, add_zero]
  have hh := hb d i.val
  rw [hs] at hh
  simpa only [d, dite_eq_left i.property] using hh

/-- Nonzero independent coefficient rescalings do not change the spanned subspace. -/
theorem span_mul_eq {ι : Type*} (b : ι → K) (a : ι → E) (ha : ∀ i, a i ≠ 0) :
    Submodule.span E (Set.range (fun i => (a i : K) * b i)) =
      Submodule.span E (Set.range b) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (Submodule.span E (Set.range b)).smul_mem (a i)
      (Submodule.subset_span (Set.mem_range_self i))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have h := (Submodule.span E (Set.range (fun i => (a i : K) * b i))).smul_mem
      (a i)⁻¹ (Submodule.subset_span (Set.mem_range_self i))
    have hai : (a i : K) ≠ 0 := by exact_mod_cast ha i
    change b i ∈ Submodule.span E (Set.range (fun i => (a i : K) * b i))
    simpa only [Subfield.smul_def, smul_eq_mul, Subfield.coe_inv, ← mul_assoc,
      inv_mul_cancel₀ hai, one_mul] using h

end Valuation
