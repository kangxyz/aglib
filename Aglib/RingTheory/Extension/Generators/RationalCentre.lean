/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-! # Actual generators and coordinates at a rational residue centre

The centre ideal is computed from the original residue point, and target divided
coordinates are obtained from the actual residue square and uniformizer.
-/

@[expose] public noncomputable section

open MvPolynomial IsLocalRing

namespace Algebra.Generators

variable {R A ι : Type*} [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]

/-- Actual lifts of the residue coordinates generate the entire residue-point kernel. -/
theorem ker_residuePoint_eq_span (P : Generators R A ι) (p : R)
    (hp : maximalIdeal R = Ideal.span {p}) (φ : A →ₐ[R] ResidueField R)
    (a : ι → R) (ha : ∀ i, residue R (a i) = φ (P.val i)) :
    RingHom.ker φ.toRingHom = Ideal.span
      (insert (algebraMap R A p) (Set.range (fun i => P.val i - algebraMap R A (a i)))) := by
  let J : Ideal A := Ideal.span
    (insert (algebraMap R A p) (Set.range (fun i => P.val i - algebraMap R A (a i))))
  have hpJ : algebraMap R A p ∈ J := Ideal.subset_span (Set.mem_insert _ _)
  have hgJ (i : ι) : P.val i - algebraMap R A (a i) ∈ J :=
    Ideal.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  have hle : J ≤ RingHom.ker φ.toRingHom := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases hx with rfl | ⟨i, rfl⟩
    · change φ (algebraMap R A p) = 0
      rw [φ.commutes]
      apply (residue_eq_zero_iff _).mpr
      rw [hp]
      exact Ideal.subset_span (Set.mem_singleton p)
    · change φ (P.val i - algebraMap R A (a i)) = 0
      rw [map_sub, φ.commutes]
      change φ (P.val i) - residue R (a i) = 0
      rw [ha, sub_self]
  apply le_antisymm _ hle
  intro b hb
  let q : A →ₐ[R] A ⧸ J := Ideal.Quotient.mkₐ R J
  have hg (i : ι) : q (P.val i) = algebraMap R (A ⧸ J) (a i) := by
    have h : q (P.val i - algebraMap R A (a i)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hgJ i)
    simpa only [map_sub, q.commutes, sub_eq_zero] using h
  have hq : q.comp (aeval P.val) = (Algebra.ofId R (A ⧸ J)).comp (aeval a) := by
    ext i
    simpa only [AlgHom.comp_apply, aeval_X, Algebra.ofId_apply] using hg i
  have hφ : φ.comp (aeval P.val) = (Algebra.ofId R (ResidueField R)).comp (aeval a) := by
    ext i
    simp only [AlgHom.comp_apply, aeval_X, Algebra.ofId_apply]
    change φ (P.val i) = residue R (a i)
    exact (ha i).symm
  obtain ⟨f, rfl⟩ := P.aeval_val_surjective b
  have hr : residue R (aeval a f) = 0 := by
    have h := DFunLike.congr_fun hφ f
    change φ (aeval P.val f) = residue R (aeval a f) at h
    exact h.symm.trans hb
  have hrmem : aeval a f ∈ Ideal.span ({p} : Set R) := by
    rw [← hp]
    exact (residue_eq_zero_iff _).mp hr
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hrmem
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (aeval P.val f) = 0
  have h := DFunLike.congr_fun hq f
  change q (aeval P.val f) = algebraMap R (A ⧸ J) (aeval a f) at h
  rw [h, hc, map_mul]
  have hz : algebraMap R (A ⧸ J) p = 0 := by
    change q (algebraMap R A p) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpJ
  rw [hz, zero_mul]

/-- The original residue map supplies actual coefficient lifts and the centre ideal. -/
theorem exists_residueCentre (P : Generators R A ι) (p : R)
    (hp : maximalIdeal R = Ideal.span {p}) (φ : A →ₐ[R] ResidueField R) :
    ∃ a : ι → R, (∀ i, residue R (a i) = φ (P.val i)) ∧
      RingHom.ker φ.toRingHom = Ideal.span
        (insert (algebraMap R A p) (Set.range (fun i => P.val i - algebraMap R A (a i)))) := by
  choose a ha using fun i => residue_surjective (φ (P.val i))
  exact ⟨a, ha, P.ker_residuePoint_eq_span p hp φ a ha⟩

/-- A genuine residue square and uniformizer give the rational-centre point coordinates. -/
theorem exists_residueCentre_and_dividedPoint {S : Type*} [CommRing S]
    [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    (P : Generators R A ι) (p : R) (hp : maximalIdeal R = Ideal.span {p})
    (φ : A →ₐ[R] ResidueField R) (χ : A →ₐ[R] S)
    (e : ResidueField R →+* ResidueField S)
    (hres : ∀ b, residue S (χ b) = e (φ b))
    (hpS : Irreducible (algebraMap R S p)) :
    ∃ a : ι → R, ∃ z : ι → S,
      RingHom.ker φ.toRingHom = Ideal.span
        (insert (algebraMap R A p) (Set.range (fun i => P.val i - algebraMap R A (a i)))) ∧
      ∀ i, χ (P.val i) = algebraMap R S (a i) + algebraMap R S p * z i := by
  obtain ⟨a, ha, hker⟩ := P.exists_residueCentre p hp φ
  have hdiv (i : ι) : algebraMap R S p ∣ χ (P.val i) - algebraMap R S (a i) := by
    apply Ideal.mem_span_singleton.mp
    rw [← hpS.maximalIdeal_eq]
    apply (residue_eq_zero_iff _).mp
    rw [map_sub, hres]
    have hbase := hres (algebraMap R A (a i))
    rw [χ.commutes, φ.commutes] at hbase
    change residue S (algebraMap R S (a i)) = e (residue R (a i)) at hbase
    rw [hbase, ha, sub_self]
  choose z hz using hdiv
  refine ⟨a, z, hker, fun i => ?_⟩
  exact (sub_eq_iff_eq_add.mp (hz i)).trans (add_comm _ _)

end Algebra.Generators
