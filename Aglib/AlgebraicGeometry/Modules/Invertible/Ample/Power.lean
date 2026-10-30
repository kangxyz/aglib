/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Ample.Basic

/-! # Ampleness descends from a positive original tensor power -/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- If a positive original tensor power is ample, the original bundle is
ample. The affine opens and sections are transported through the actual
power-class equation; no separatedness or projective model is needed. -/
theorem LineBundle.IsAmple.of_tensorPower {X : Scheme.{u}} (L : LineBundle X)
    (n : ℕ) (hn : 0 < n) (h : (tensorPowerLineBundle X L n).IsAmple) : L.IsAmple := by
  refine ⟨h.1, ?_⟩
  intro x
  obtain ⟨m, hm, s, hs, hx⟩ := h.2 x
  have hc : classOf X (tensorPowerLineBundle X (tensorPowerLineBundle X L n) m) =
      classOf X (tensorPowerLineBundle X L (m * n)) := by
    simp only [classOf_tensorPower, smul_smul]
  obtain ⟨e⟩ := (class_eq_iff X _ _).mp hc
  refine ⟨m * n, Nat.mul_pos hm hn, e.hom.val.app (op ⊤) s, ?_, ?_⟩
  · rwa [nonvanishingOpen_iso]
  · rwa [nonvanishingOpen_iso]

end AlgebraicGeometry.Scheme.Modules.Invertible
