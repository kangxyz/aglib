/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Dense range under an open base change

Relocated from R5 baseline `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Existing mathematical declarations and explicit source boundaries are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Limits.DenseRange` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`db42d7e9067a9ba0d1a5d251fe71d10cb4b871e41c5b376cd05833c73a3d5906`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An actual cartesian square pulls a dense range back to a dense range
when the other map is open. No scheme-point joint injectivity is used. -/
theorem denseRange_of_open_pullback {W X Y S : Scheme.{u}}
    (a : W ⟶ X) (b : W ⟶ Y) (c : X ⟶ S) (d : Y ⟶ S)
    (h : IsPullback a b c d) (hc : IsOpenMap c) (hd : DenseRange d) : DenseRange a := by
  have hr : Set.range a = Set.range (pullback.fst c d) := by
    rw [← h.isoPullback_hom_fst]
    change Set.range ((pullback.fst c d) ∘ h.isoPullback.hom) = _
    rw [Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ]
  change Dense (Set.range a)
  rw [hr, Scheme.Pullback.range_fst]
  exact hd.preimage hc

end AlgebraicGeometry.Scheme.Hom
