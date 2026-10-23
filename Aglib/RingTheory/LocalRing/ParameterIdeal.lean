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
# Actual parameter ideals in low-dimensional local rings

The native height theorem gives a finite generating set whose ideal has
the actual maximal ideal as a minimal prime. Locality identifies its
radical with that maximal ideal. In dimension at most two, any prescribed
nonzero nonunit in a local domain can be completed by one element to
such an ideal. The intermediate quotient need not be reduced or regular.
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

/-- A prescribed nonzero nonunit in a local Noetherian domain of
dimension at most two extends to an actual maximal-primary parameter
ideal with one additional element. -/
theorem exists_parameter_pair_containing
    (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 2 R] (a : R) (ha0 : a ≠ 0) (ha : a ∈ maximalIdeal R) :
    ∃ x : R, x ∈ maximalIdeal R ∧
      (Ideal.span {a} ⊔ Ideal.span {x}).radical = maximalIdeal R := by
  let I : Ideal R := Ideal.span {a}
  let Q := R ⧸ I
  let q : R →+* Q := Ideal.Quotient.mk I
  have hI : I ≠ ⊤ := fun h ↦ ha (Ideal.span_singleton_eq_top.mp h)
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hI
  let : IsLocalRing Q := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  let : IsNoetherianRing Q := isNoetherianRing_of_surjective R Q q Ideal.Quotient.mk_surjective
  let : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  let : Ring.KrullDimLE 1 Q := by
    apply Ring.krullDimLE_iff.mpr
    apply ENat.WithBot.add_le_add_one_right_iff.mp
    have hdim := ringKrullDim_succ_le_of_surjective q Ideal.Quotient.mk_surjective
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha0)
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a))
    convert hdim.trans
      (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 2 R)) using 1
    norm_num
  obtain ⟨xbar, hxbar, hradbar⟩ := exists_principal_parameter_of_dimLE_one Q
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective xbar
  change q x = xbar at hx
  have hxmem : x ∈ maximalIdeal R := by
    rw [← IsLocalRing.maximalIdeal_comap q]
    change q x ∈ maximalIdeal Q
    rwa [hx]
  let J : Ideal R := I ⊔ Ideal.span {x}
  have hmap : J.map q = Ideal.span {xbar} := by
    change (I ⊔ Ideal.span {x}).map q = _
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq,
      Ideal.map_span, Set.image_singleton, hx]
  have hrad : (J.map q).radical = maximalIdeal Q := by rw [hmap]; exact hradbar
  have hcomap := congrArg (Ideal.comap q) hrad
  rw [Ideal.comap_radical, Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective,
    show RingHom.ker q = I from Ideal.mk_ker,
    sup_eq_left.mpr (show I ≤ J from le_sup_left), IsLocalRing.maximalIdeal_comap q] at hcomap
  exact ⟨x, hxmem, hcomap⟩

end IsLocalRing
