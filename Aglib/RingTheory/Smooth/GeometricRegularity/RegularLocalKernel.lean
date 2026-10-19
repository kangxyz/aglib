/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RegularLocalRing.Domain
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Kernels of regular local quotients

If a regular local ring has a regular local quotient, the kernel has no extra relations in
the square of the maximal ideal: `I ∩ m² = mI`. The proof inducts on the dimension, killing
a parameter in the kernel. An ideal contained in `m²` preserves the minimal generator number
of the maximal ideal by Nakayama's lemma, and therefore must vanish by dimension drop.
-/

@[expose] public section

noncomputable section

universe u

open IsLocalRing
open scoped nonZeroDivisors

namespace IsRegularLocalRing

private theorem spanFinrank_maximalIdeal_le_quotient_of_le_sq
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsLocalRing (R ⧸ I)] (hI : I ≤ maximalIdeal R ^ 2) :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal (R ⧸ I)).spanFinrank := by
  classical
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  let : IsLocalHom q := IsLocalHom.of_surjective q hq
  let g : R ⧸ I → R := Function.surjInv hq
  have hg (y : R ⧸ I) : q (g y) = y := Function.surjInv_eq hq y
  obtain ⟨s, hcard, hs⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (maximalIdeal (R ⧸ I)).fg_of_isNoetherianRing
  let t : Finset R := s.image g
  have himage : q '' (t : Set R) = (s : Set (R ⧸ I)) := by
    ext y
    simp only [t, Finset.coe_image, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [hg] using hz
    · intro hy
      exact ⟨g y, ⟨y, hy, rfl⟩, hg y⟩
  have hmap : (Ideal.span (t : Set R)).map q = maximalIdeal (R ⧸ I) := by
    rw [Ideal.map_span, himage]
    exact hs
  have hsup : Ideal.span (t : Set R) ⊔ I = maximalIdeal R := by
    have he := congrArg (Ideal.comap q) hmap
    rwa [Ideal.comap_map_of_surjective q hq, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      maximalIdeal_comap q] at he
  have hspan : maximalIdeal R = Ideal.span (t : Set R) := by
    apply le_antisymm
    · apply Submodule.le_of_le_smul_of_le_jacobson_bot
        (I := maximalIdeal R) (N := Ideal.span (t : Set R)) (N' := maximalIdeal R)
        (maximalIdeal R).fg_of_isNoetherianRing
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
      rw [smul_eq_mul, ← pow_two]
      exact hsup.symm.le.trans (sup_le_sup_left hI _)
    · rw [← hsup]
      exact le_sup_left
  rw [hspan]
  apply (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet t)).trans
  rw [Set.ncard_coe_finset]
  exact Finset.card_image_le.trans hcard.le

private theorem eq_bot_of_le_maximalIdeal_sq
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (I : Ideal R) [IsRegularLocalRing (R ⧸ I)] (hI : I ≤ maximalIdeal R ^ 2) : I = ⊥ := by
  let : IsDomain R := isDomain_of_regularLocal R
  have hdim : ringKrullDim R ≤ ringKrullDim (R ⧸ I) := by
    rw [← spanFinrank_maximalIdeal, ← spanFinrank_maximalIdeal]
    exact_mod_cast spanFinrank_maximalIdeal_le_quotient_of_le_sq R I hI
  apply eq_bot_iff.mpr
  intro r hr
  rw [Ideal.mem_bot]
  by_contra hr0
  have hdrop := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero hr0)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  have hbad := hdrop.trans hdim
  rw [← spanFinrank_maximalIdeal (R := R ⧸ I)] at hbad
  have hnat : (maximalIdeal (R ⧸ I)).spanFinrank + 1 ≤
      (maximalIdeal (R ⧸ I)).spanFinrank := by
    exact_mod_cast hbad
  omega

private theorem inf_maximalIdeal_sq_eq_mul_of_dimension
    (d : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hd : ringKrullDim R = (d : ℕ)) (I : Ideal R) [IsRegularLocalRing (R ⧸ I)] :
    I ⊓ maximalIdeal R ^ 2 = maximalIdeal R * I := by
  induction d generalizing R with
  | zero =>
    have hf := isField_of_regularLocal_dimension_zero R (by simpa using hd)
    have hm := isField_iff_maximalIdeal_eq.mp hf
    simp [hm]
  | succ d ih =>
    by_cases hI2 : I ≤ maximalIdeal R ^ 2
    · rw [eq_bot_of_le_maximalIdeal_sq R I hI2]
      simp
    · obtain ⟨x, hxI, hx2⟩ := SetLike.not_le_iff_exists.mp hI2
      have hIm : I ≤ maximalIdeal R :=
        le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp inferInstance)
      have hmul : maximalIdeal R * I ≤ maximalIdeal R ^ 2 := by
        simpa only [pow_two] using Ideal.mul_mono_right hIm
      obtain ⟨hreg, hdim⟩ := regularLocal_quotient_parameter R d hd x (hIm hxI) hx2
      let S := R ⧸ Ideal.span {x}
      let q : R →+* S := Ideal.Quotient.mk (Ideal.span {x})
      let : IsRegularLocalRing S := hreg
      let K := I.map q
      have hxle : Ideal.span {x} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hxI
      let e : S ⧸ K ≃+* R ⧸ I := DoubleQuot.quotQuotEquivQuotOfLE hxle
      let : IsRegularLocalRing (S ⧸ K) := of_ringEquiv e.symm
      have hind : K ⊓ maximalIdeal S ^ 2 = maximalIdeal S * K := ih S hdim K
      have hmapm : (maximalIdeal R).map q = maximalIdeal S :=
        map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective
      apply le_antisymm
      · intro a ha
        have hqa : q a ∈ K ⊓ maximalIdeal S ^ 2 := by
          refine ⟨Ideal.mem_map_of_mem q ha.1, ?_⟩
          rw [← hmapm, ← Ideal.map_pow]
          exact Ideal.mem_map_of_mem q ha.2
        have hqa' : q a ∈ (maximalIdeal R * I).map q := by
          rw [Ideal.map_mul, hmapm]
          exact hind ▸ hqa
        obtain ⟨b, hb, hba⟩ :=
          (Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp hqa'
        have hab : a - b ∈ Ideal.span {x} := by
          apply Ideal.Quotient.eq_zero_iff_mem.mp
          change q (a - b) = 0
          rw [map_sub, hba, sub_self]
        obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hab
        have hrx : r * x ∈ maximalIdeal R ^ 2 := by
          rw [hr]
          exact (maximalIdeal R ^ 2).sub_mem ha.2 (hmul hb)
        have hrm : r ∈ maximalIdeal R := by
          by_contra hrm
          have hunit : IsUnit r := by
            simpa only [mem_maximalIdeal, mem_nonunits_iff, not_not] using hrm
          exact hx2 ((maximalIdeal R ^ 2).unit_mul_mem_iff_mem hunit |>.mp hrx)
        have hab' : a - b ∈ maximalIdeal R * I :=
          hr ▸ Ideal.mul_mem_mul hrm hxI
        simpa only [sub_add_cancel] using (maximalIdeal R * I).add_mem hab' hb
      · exact le_inf Ideal.mul_le_right hmul

/-- The kernel of a regular local quotient has no additional relation in the square of the
maximal ideal. Equivalently, its conormal space injects into the ambient cotangent space. -/
theorem inf_maximalIdeal_sq_eq_mul
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (I : Ideal R) [IsRegularLocalRing (R ⧸ I)] :
    I ⊓ maximalIdeal R ^ 2 = maximalIdeal R * I :=
  inf_maximalIdeal_sq_eq_mul_of_dimension (maximalIdeal R).spanFinrank R
    spanFinrank_maximalIdeal.symm I

end IsRegularLocalRing
