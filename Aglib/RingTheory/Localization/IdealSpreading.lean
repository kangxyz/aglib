/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Finiteness.Defs

/-! # Spreading equality of finitely generated ideals to one principal open

Only finite generation of the two ideals is required. The ambient ring need not
be Noetherian or a domain. All maps are the actual canonical localization maps.
-/

@[expose] public noncomputable section

namespace Ideal

variable {A : Type*} [CommRing A] (q : Ideal A) [q.IsPrime]

/-- Finitely many denominators outside a prime admit one common denominator. -/
theorem exists_common_denominator (J : Ideal A) (t : Finset A)
    (h : ∀ x ∈ t, ∃ s : A, s ∉ q ∧ s * x ∈ J) :
    ∃ s : A, s ∉ q ∧ ∀ x ∈ t, s * x ∈ J := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, q.one_notMem, by simp⟩
  | @insert a t hat ih =>
      obtain ⟨u, hu, hua⟩ := h a (Finset.mem_insert_self a t)
      obtain ⟨v, hv, hvt⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
      refine ⟨u * v, q.primeCompl.mul_mem hu hv, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simpa only [mul_assoc, mul_comm, mul_left_comm] using J.mul_mem_left v hua
      · simpa only [mul_assoc] using J.mul_mem_left u (hvt x hx)

/-- A finitely generated ideal contained in another after prime localization has
one actual denominator clearing the entire inclusion. -/
theorem exists_mul_mem_of_map_le_atPrime (I J : Ideal A) (hI : I.FG)
    (h : I.map (algebraMap A (Localization.AtPrime q)) ≤
      J.map (algebraMap A (Localization.AtPrime q))) :
    ∃ s : A, s ∉ q ∧ ∀ x ∈ I, s * x ∈ J := by
  classical
  obtain ⟨t, ht⟩ := hI
  have hgen : ∀ x ∈ t, ∃ s : A, s ∉ q ∧ s * x ∈ J := by
    intro x hx
    have hxi : x ∈ I := ht ▸ Ideal.subset_span hx
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl
      (Localization.AtPrime q) J x).mp (h (Ideal.mem_map_of_mem _ hxi))
  obtain ⟨s, hs, hst⟩ := exists_common_denominator q J t hgen
  refine ⟨s, hs, ?_⟩
  intro x hx
  rw [← ht] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hst x hx
  | zero => simp
  | add x y hx hy hx' hy' => simpa only [mul_add] using J.add_mem hx' hy'
  | smul a x hx hx' =>
      simpa only [smul_eq_mul, mul_assoc, mul_left_comm] using J.mul_mem_left a hx'

/-- A denominator clearing an inclusion makes it hold on its actual principal open. -/
theorem map_le_away_of_mul_mem (I J : Ideal A) (s : A)
    (h : ∀ x ∈ I, s * x ∈ J) :
    I.map (algebraMap A (Localization.Away s)) ≤
      J.map (algebraMap A (Localization.Away s)) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  change algebraMap A (Localization.Away s) x ∈ J.map (algebraMap A (Localization.Away s))
  apply (Ideal.unit_mul_mem_iff_mem _
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away s) s)).mp
  rw [← map_mul]
  exact Ideal.mem_map_of_mem _ (h x hx)

/-- Equality of two finite ideals at a prime already holds on a single actual principal open. -/
theorem exists_away_map_eq_of_atPrime_map_eq (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (h : I.map (algebraMap A (Localization.AtPrime q)) =
      J.map (algebraMap A (Localization.AtPrime q))) :
    ∃ s : A, s ∉ q ∧
      I.map (algebraMap A (Localization.Away s)) =
        J.map (algebraMap A (Localization.Away s)) := by
  obtain ⟨u, hu, huIJ⟩ := exists_mul_mem_of_map_le_atPrime q I J hI h.le
  obtain ⟨v, hv, hvJI⟩ := exists_mul_mem_of_map_le_atPrime q J I hJ h.ge
  refine ⟨u * v, q.primeCompl.mul_mem hu hv, le_antisymm ?_ ?_⟩
  · apply map_le_away_of_mul_mem
    intro x hx
    simpa only [mul_assoc, mul_comm, mul_left_comm] using J.mul_mem_left v (huIJ x hx)
  · apply map_le_away_of_mul_mem
    intro x hx
    simpa only [mul_assoc] using I.mul_mem_left u (hvJI x hx)

end Ideal
