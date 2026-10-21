/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.RegularLocalRing.Parameters
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Regular systems of parameters

A regular local ring has a regular sequence generating its maximal ideal, with
length equal to its Krull dimension. The construction iterates the actual
regular-parameter quotient and lifts a sequence from that quotient. This is a
prerequisite for the projective dimension of the residue field.
-/

@[expose] public section

noncomputable section

universe u

open IsLocalRing RingTheory.Sequence
open scoped Pointwise

namespace IsRegularLocalRing

/-- A regular local ring of dimension `d` admits a regular system of `d` parameters. -/
theorem exists_regular_sequence_maximalIdeal (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (d : ℕ) (hd : ringKrullDim R = (d : ℕ)) :
    ∃ rs : List R, rs.length = d ∧ IsRegular R rs ∧
      Ideal.ofList rs = maximalIdeal R := by
  induction d generalizing R with
  | zero =>
    have hf := isField_of_regularLocal_dimension_zero R (by simpa using hd)
    have hm : maximalIdeal R = ⊥ := isField_iff_maximalIdeal_eq.mp hf
    refine ⟨[], rfl, ?_, by simpa using hm.symm⟩
    exact ⟨IsWeaklyRegular.nil R R, by simp⟩
  | succ d ih =>
    obtain ⟨x, hx, hxr, hQ, hdim⟩ := exists_regular_parameter R d hd
    let Q := R ⧸ Ideal.span {x}
    let q : R →+* Q := Ideal.Quotient.mk (Ideal.span {x})
    have : IsRegularLocalRing Q := hQ
    have : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
    obtain ⟨ss, hlen, hreg, hspan⟩ := ih Q hdim
    obtain ⟨rs, hrs⟩ := (List.map_surjective_iff.mpr
      (Ideal.Quotient.mk_surjective : Function.Surjective q)) ss
    have hlenrs : rs.length = d := by
      simpa using (congrArg List.length hrs).trans hlen
    have hquot : x • (⊤ : Submodule R R) = Ideal.span {x} := by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
    let e : QuotSMulTop x R ≃ₗ[R] Q := Submodule.quotEquivOfEq _ _ hquot
    have ht : IsWeaklyRegular Q rs :=
      (isWeaklyRegular_map_algebraMap_iff Q Q rs).mp (by
        change IsWeaklyRegular Q (rs.map q)
        rw [hrs]
        exact hreg.toIsWeaklyRegular)
    have hw : IsWeaklyRegular R (x :: rs) :=
      IsWeaklyRegular.cons hxr ((e.isWeaklyRegular_congr rs).mpr ht)
    have hqx : q x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton x))
    have hm : Ideal.ofList (x :: rs) = maximalIdeal R := by
      have hmap : (Ideal.ofList (x :: rs)).map q = maximalIdeal Q := by
        rw [Ideal.map_ofList, List.map_cons, hqx, hrs, Ideal.ofList_cons]
        simpa using hspan
      have hc := congrArg (Ideal.comap q) hmap
      rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
        maximalIdeal_comap q, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
        Ideal.ofList_cons, sup_assoc, sup_comm (Ideal.ofList rs), ← sup_assoc,
        sup_idem] at hc
      simpa only [Ideal.ofList_cons] using hc
    refine ⟨x :: rs, by simp [hlenrs], ⟨hw, ?_⟩, hm⟩
    rw [hm, smul_eq_mul, Ideal.mul_top]
    exact (maximalIdeal.isMaximal R).ne_top.symm

end IsRegularLocalRing
