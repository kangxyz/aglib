/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Ample.Tensor
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! A single positive power of an ample bundle has a cover by original sections. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X : Scheme.{u}}

/-- A finite set of original ample nonvanishing opens yields a common
positive tensor power whose original global sections cover the scheme. -/
theorem LineBundle.IsAmple.exists_tensorPower_nonvanishing_cover {L : LineBundle X}
    (hL : L.IsAmple) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : X, ∃ s : Γ((tensorPowerLineBundle X L n).val, ⊤),
      IsAffineOpen (nonvanishingOpen (tensorPowerLineBundle X L n) s) ∧
        x ∈ nonvanishingOpen (tensorPowerLineBundle X L n) s := by
  classical
  let : CompactSpace X := hL.1
  let I := Σ n : ℕ, {s : Γ((tensorPowerLineBundle X L n).val, ⊤) //
    0 < n ∧ IsAffineOpen (nonvanishingOpen (tensorPowerLineBundle X L n) s)}
  let U (i : I) := nonvanishingOpen (tensorPowerLineBundle X L i.1) i.2.val
  have hcover : (Set.univ : Set X) ⊆ ⋃ i : I, (U i : Set X) := by
    intro x _
    obtain ⟨n, hn, s, hs, hx⟩ := hL.2 x
    exact Set.mem_iUnion.mpr ⟨⟨n, s, hn, hs⟩, hx⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun i : I => (U i : Set X))
    (fun i => (U i).isOpen) hcover
  let n := ∏ i ∈ t, i.1
  have hn : 0 < n := Finset.prod_pos (fun i _ => i.2.property.1)
  refine ⟨n, hn, fun x => ?_⟩
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun i : I => i.1) hi
  have hmpos : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro h
    rw [h, Nat.mul_zero] at hm
    exact (Nat.ne_of_gt hn) hm
  let A := tensorPowerLineBundle X (tensorPowerLineBundle X L i.1) m
  let B := tensorPowerLineBundle X L n
  obtain ⟨s, hs⟩ := exists_tensorPowerSection_nonvanishing
    (tensorPowerLineBundle X L i.1) i.2.val m hmpos
  have hc : classOf X A = classOf X B := by
    simp only [A, B, classOf_tensorPower, smul_smul]
    rw [Nat.mul_comm m i.1, ← hm]
  obtain ⟨e⟩ := (class_eq_iff X A B).mp hc
  have h : nonvanishingOpen B (e.hom.val.app (op ⊤) s) = U i := by
    rw [nonvanishingOpen_iso, hs]
  exact ⟨e.hom.val.app (op ⊤) s, h.symm ▸ i.2.property.2, h.symm ▸ hx⟩

end AlgebraicGeometry.Scheme.Modules.Invertible
