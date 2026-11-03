/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Actual finite parameter families in local rings

The native height theorem gives a finite generating set whose ideal has
the actual maximal ideal as a minimal prime. Locality identifies its
radical with that maximal ideal. Any prescribed nonzero nonunit in a finite-dimensional local domain
can be completed by a finite family to such an ideal.
The intermediate quotient need not be reduced or regular.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace IsLocalRing

private theorem radical_eq_maximalIdeal_of_mem_minimalPrimes
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (h : maximalIdeal R ∈ I.minimalPrimes) : I.radical = maximalIdeal R := by
  apply le_antisymm
  · exact (maximalIdeal.isMaximal R).isPrime.radical_le_iff.mpr h.le
  · rw [I.radical_eq_sInf]
    apply le_sInf
    intro P hP
    exact h.2 ⟨hP.2, hP.1⟩ (le_maximalIdeal hP.2.ne_top)

/-- A Noetherian local ring has an actual parameter set of cardinality
its finite Krull dimension, with maximal radical. -/
theorem exists_parameter_finset (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (d : ℕ) (hd : ringKrullDim R = (d : ℕ)) :
    ∃ s : Finset R, s.card = d ∧ (Ideal.span (s : Set R)).radical = maximalIdeal R := by
  classical
  obtain ⟨s, hs, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal R)
  have hm : (maximalIdeal R).height = (d : ℕ∞) :=
    WithBot.coe_injective (maximalIdeal_height_eq_ringKrullDim.trans hd)
  refine ⟨s, ?_, radical_eq_maximalIdeal_of_mem_minimalPrimes _ hs⟩
  rw [hm] at hcard
  exact_mod_cast hcard

/-- In dimension at most one, one element generates an ideal whose
radical is the actual maximal ideal, including the zero-dimensional case. -/
theorem exists_principal_parameter_of_dimLE_one
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] :
    ∃ x : R, x ∈ maximalIdeal R ∧ (Ideal.span {x}).radical = maximalIdeal R := by
  classical
  obtain ⟨s, hs, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal R)
  have hm : (maximalIdeal R).height ≤ 1 := by
    apply WithBot.coe_le_coe.mp
    rw [maximalIdeal_height_eq_ringKrullDim]
    exact Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 R)
  have hcard' : s.card ≤ 1 := by
    have h : (s.card : ℕ∞) ≤ 1 := by rw [hcard]; exact hm
    exact_mod_cast h
  have hrad := radical_eq_maximalIdeal_of_mem_minimalPrimes _ hs
  by_cases hs0 : s = ∅
  · exact ⟨0, Ideal.zero_mem _, by simpa [hs0] using hrad⟩
  · have hsne : s.card ≠ 0 := Finset.card_eq_zero.not.mpr hs0
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (show s.card = 1 by omega)
    refine ⟨x, hs.le (Ideal.subset_span (by simp)), ?_⟩
    simpa using hrad

/-- A prescribed nonzero nonunit extends to a maximal-primary parameter
family with at most the remaining dimension many elements, padded by zero. -/
theorem exists_parameter_family_containing
    (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ) (hd : ringKrullDim R ≤ ((d + 1 : ℕ) : ℕ∞))
    (a : R) (ha0 : a ≠ 0) (ha : a ∈ maximalIdeal R) :
    ∃ x : Fin d → R, (∀ i, x i ∈ maximalIdeal R) ∧
      (Ideal.span {a} ⊔ Ideal.span (Set.range x)).radical = maximalIdeal R := by
  classical
  let I : Ideal R := Ideal.span {a}
  let Q := R ⧸ I
  let q : R →+* Q := Ideal.Quotient.mk I
  have hI : I ≠ ⊤ := fun h ↦ ha (Ideal.span_singleton_eq_top.mp h)
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hI
  let : IsLocalRing Q := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  let : IsNoetherianRing Q := isNoetherianRing_of_surjective R Q q Ideal.Quotient.mk_surjective
  let : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have hdim : ringKrullDim Q ≤ (d : ℕ) := by
    apply ENat.WithBot.add_le_add_one_right_iff.mp
    have h := ringKrullDim_succ_le_of_surjective q Ideal.Quotient.mk_surjective
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha0)
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a))
    convert h.trans hd using 1; simp
  have hheight : (maximalIdeal Q).height ≤ (d : ℕ∞) := by
    apply WithBot.coe_le_coe.mp
    rwa [maximalIdeal_height_eq_ringKrullDim]
  have hfinite : (maximalIdeal Q).height ≠ ⊤ := ne_top_of_le_ne_top (by simp) hheight
  let e := (maximalIdeal Q).height.toNat
  have he : ringKrullDim Q = (e : ℕ) := by
    rw [← maximalIdeal_height_eq_ringKrullDim, ← ENat.natCast_toNat hfinite]
    rfl
  obtain ⟨s, hs, hradbar⟩ := exists_parameter_finset Q e he
  have hcard : s.card ≤ d := by
    have h : (s.card : ℕ∞) ≤ d := by rw [hs, ENat.natCast_toNat hfinite]; exact hheight
    exact_mod_cast h
  let enum : Fin s.card ≃ s := by simpa using (Fintype.equivFin s).symm
  let y : Fin d → Q := fun i ↦ if h : i.val < s.card then (enum ⟨i.val, h⟩).val else 0
  have hyspan : Ideal.span (Set.range y) = Ideal.span (s : Set Q) := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      dsimp [y]
      split
      · exact Ideal.subset_span (enum _).property
      · exact Ideal.zero_mem _
    · apply Ideal.span_le.mpr
      intro z hz
      let j := enum.symm ⟨z, hz⟩
      have hj : j.val < d := lt_of_lt_of_le j.isLt hcard
      apply Ideal.subset_span
      refine ⟨⟨j.val, hj⟩, ?_⟩
      simp only [y, dite_eq_left j.isLt]
      exact congrArg Subtype.val (enum.apply_symm_apply ⟨z, hz⟩)
  have hymem (i : Fin d) : y i ∈ maximalIdeal Q := by
    rw [← hradbar, ← hyspan]
    exact Ideal.le_radical (Ideal.subset_span (Set.mem_range_self i))
  choose x hx using fun i ↦ Ideal.Quotient.mk_surjective (y i)
  have hxmem (i : Fin d) : x i ∈ maximalIdeal R := by
    rw [← IsLocalRing.maximalIdeal_comap q]
    change q (x i) ∈ maximalIdeal Q
    rw [hx i]
    exact hymem i
  let J : Ideal R := I ⊔ Ideal.span (Set.range x)
  have hmap : J.map q = Ideal.span (Set.range y) := by
    change (I ⊔ Ideal.span (Set.range x)).map q = _
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span]
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hx i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, hx i⟩
  have hrad : (J.map q).radical = maximalIdeal Q := by rw [hmap, hyspan]; exact hradbar
  have hcomap := congrArg (Ideal.comap q) hrad
  rw [Ideal.comap_radical, Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective,
    show RingHom.ker q = I from Ideal.mk_ker,
    sup_eq_left.mpr (show I ≤ J from le_sup_left), IsLocalRing.maximalIdeal_comap q] at hcomap
  exact ⟨x, hxmem, hcomap⟩

end IsLocalRing
