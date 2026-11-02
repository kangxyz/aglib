/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Ample.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing.Tensor

/-!
# Tensor products of ample line bundles on separated schemes

Positive tensor powers of the original sections have the same nonvanishing
open. Tensoring the resulting sections, and transporting along the equality
of their original Picard classes, gives the affine covering for the product.
Separatedness is retained in this supplier, which uses intersections of affine
opens. No projective embedding, reducedness or Noetherian hypothesis is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A positive tensor power has an actual section with the same
nonvanishing open as the original section. -/
theorem exists_tensorPowerSection_nonvanishing (L : LineBundle X)
    (s : Γ(L.val, ⊤)) (n : ℕ) (hn : 0 < n) :
    ∃ t : Γ((tensorPowerLineBundle X L n).val, ⊤),
      nonvanishingOpen (tensorPowerLineBundle X L n) t = nonvanishingOpen L s := by
  induction n with
  | zero => exact (Nat.not_lt_zero _ hn).elim
  | succ n ih =>
      by_cases h : n = 0
      · subst n
        have hc : classOf X (tensorPowerLineBundle X L 1) = classOf X L := by
          rw [classOf_tensorPower, one_smul]
        obtain ⟨e⟩ := (class_eq_iff X _ _).mp hc
        exact ⟨e.inv.val.app (op ⊤) s, nonvanishingOpen_iso L _ e.symm s⟩
      · obtain ⟨t, ht⟩ := ih (Nat.pos_of_ne_zero h)
        refine ⟨moduleTensorSection X L.val (tensorPowerLineBundle X L n).val ⊤ s t, ?_⟩
        change nonvanishingOpen (tensorLineBundle X L (tensorPowerLineBundle X L n)) _ = _
        rw [nonvanishingOpen_tensor, ht, inf_idem]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tensor products preserve ampleness on separated schemes. The proof
uses the original tensor sections and tensor powers throughout. -/
theorem LineBundle.IsAmple.tensor [X.IsSeparated] {L M : LineBundle X}
    (hL : L.IsAmple) (hM : M.IsAmple) : (tensorLineBundle X L M).IsAmple := by
  refine ⟨hL.1, ?_⟩
  intro x
  obtain ⟨n, hn, s, hs, hx⟩ := hL.2 x
  obtain ⟨m, hm, t, ht, hy⟩ := hM.2 x
  obtain ⟨s', hs'⟩ := exists_tensorPowerSection_nonvanishing
    (tensorPowerLineBundle X L n) s m hm
  obtain ⟨t', ht'⟩ := exists_tensorPowerSection_nonvanishing
    (tensorPowerLineBundle X M m) t n hn
  let A := tensorPowerLineBundle X (tensorPowerLineBundle X L n) m
  let B := tensorPowerLineBundle X (tensorPowerLineBundle X M m) n
  let C := tensorPowerLineBundle X (tensorLineBundle X L M) (n * m)
  have hc : classOf X (tensorLineBundle X A B) = classOf X C := by
    simp only [A, B, C, classOf_tensor, classOf_tensorPower, smul_add, smul_smul]
    rw [Nat.mul_comm m n]
  obtain ⟨e⟩ := (class_eq_iff X _ _).mp hc
  let r := moduleTensorSection X A.val B.val ⊤ s' t'
  have hr : nonvanishingOpen (tensorLineBundle X A B) r =
      nonvanishingOpen (tensorPowerLineBundle X L n) s ⊓
        nonvanishingOpen (tensorPowerLineBundle X M m) t := by
    rw [nonvanishingOpen_tensor, hs', ht']
  refine ⟨n * m, Nat.mul_pos hn hm, e.hom.val.app (op ⊤) r, ?_, ?_⟩
  · rw [nonvanishingOpen_iso, hr]
    exact hs.inf ht
  · rw [nonvanishingOpen_iso, hr]
    exact ⟨hx, hy⟩

/-- Every positive original tensor power of an ample line bundle is ample.
The separatedness hypothesis is that of the tensor-product supplier. -/
theorem LineBundle.IsAmple.tensorPower [X.IsSeparated] {L : LineBundle X}
    (hL : L.IsAmple) (n : ℕ) (hn : 0 < n) : (tensorPowerLineBundle X L n).IsAmple := by
  induction n with
  | zero => exact (Nat.not_lt_zero _ hn).elim
  | succ n ih =>
      by_cases h : n = 0
      · subst n
        exact hL.of_classOf_eq (by simp only [classOf_tensorPower, Nat.zero_add, one_smul])
      · exact hL.tensor (ih (Nat.pos_of_ne_zero h))

end AlgebraicGeometry.Scheme.Modules.Invertible
