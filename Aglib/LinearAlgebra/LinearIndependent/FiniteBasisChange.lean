/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Tactic.Ring

/-!
# Finite basis changes preserve linear independence
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace LinearIndependent

/-- Finite basis change over the source coefficient field remains invertible
in the target coefficient field. Only the two finite spans occur in this proof;
no basis of either ambient field is selected. -/
theorem mul_of_span_eq
    {K L ι κ ρ : Type*} [Field K] [Field L]
    [Finite ι] [Finite κ] [Finite ρ]
    (E : Subfield K) (F : Subfield L) (f : K →+* L) (σ : E →+* F)
    (hσ : ∀ c : E, f c = (σ c : L))
    {a : ι → K} {b : κ → K}
    (ha : LinearIndependent E a) (hb : LinearIndependent E b)
    (hspan : Submodule.span E (Set.range a) = Submodule.span E (Set.range b))
    (z : ρ → L)
    (hprod : LinearIndependent F (fun q : ρ × κ => f (b q.2) * z q.1)) :
    LinearIndependent F (fun q : ρ × ι => f (a q.2) * z q.1) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  let := Fintype.ofFinite ρ
  let A := Module.Basis.span ha
  let B := Module.Basis.span hb
  have hamem (i : ι) : a i ∈ Submodule.span E (Set.range b) := by
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hbmem (j : κ) : b j ∈ Submodule.span E (Set.range a) := by
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self j)
  let C (j : κ) (i : ι) : E := B.repr ⟨a i, hamem i⟩ j
  let D (i : ι) (j : κ) : E := A.repr ⟨b j, hbmem j⟩ i
  have hexp (i : ι) : ∑ j, (C j i : K) * b j = a i := by
    simpa only [C, B, Submodule.coe_sum, Submodule.coe_smul,
      Module.Basis.coe_span_apply, Subfield.smul_def, smul_eq_mul] using
      congrArg Subtype.val (B.sum_repr ⟨a i, hamem i⟩)
  have hCD (i i' : ι) : ∑ j, C j i * D i' j = if i = i' then 1 else 0 := by
    have heq : (∑ j, C j i • (⟨b j, hbmem j⟩ : Submodule.span E (Set.range a))) =
        ⟨a i, Submodule.subset_span (Set.mem_range_self i)⟩ := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Subfield.smul_def, smul_eq_mul]
        using hexp i
    have hh := congrArg (fun x => A.repr x i') heq
    simpa only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul, D, A, Module.Basis.span_repr_eq_single, Finsupp.single_apply] using hh
  have hfexp (i : ι) : f (a i) = ∑ j, (σ (C j i) : L) * f (b j) := by
    rw [← hexp i, map_sum]
    simp only [map_mul, hσ]
  apply Fintype.linearIndependent_iff.mpr
  intro t ht
  let u (q : ρ × κ) : F := ∑ i, t (q.1, i) * σ (C q.2 i)
  have hu : ∀ q, u q = 0 := by
    apply Fintype.linearIndependent_iff.mp hprod u
    change ∑ q : ρ × κ, (u q : L) * (f (b q.2) * z q.1) = 0
    change ∑ q : ρ × ι, (t q : L) * (f (a q.2) * z q.1) = 0 at ht
    rw [Fintype.sum_prod_type] at ht ⊢
    calc
      _ = ∑ e : ρ, ∑ i : ι, (t (e, i) : L) * (f (a i) * z e) := by
        apply Finset.sum_congr rfl
        intro e he
        simp only [u, AddSubmonoidClass.coe_finsetSum, Subfield.coe_mul, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hfexp, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := ht
  rintro ⟨e, i'⟩
  have hz : ∑ j, u (e, j) * σ (D i' j) = 0 := by simp only [hu, zero_mul, Finset.sum_const_zero]
  calc
    t (e, i') = ∑ i, t (e, i) * (if i = i' then 1 else 0) := by simp
    _ = ∑ i, t (e, i) * σ (∑ j, C j i * D i' j) := by
      simp only [hCD, apply_ite, map_one, map_zero]
    _ = ∑ j, u (e, j) * σ (D i' j) := by
      simp only [map_sum, map_mul, Finset.mul_sum, u, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    _ = 0 := hz

end LinearIndependent
