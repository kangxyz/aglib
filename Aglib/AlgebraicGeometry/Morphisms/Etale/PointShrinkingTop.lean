/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointShrinking

/-!
# Cartesian centres have the full shrinking open

Source: `lean/R5Lab/Aglib/AlgebraicGeometry/Morphisms/Etale/PointShrinkingTop.lean`.
Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `7965ab8ed106bcd021da2f71bc447816db3878f5a80b9fcb346cc75ef2bd6e9b`.
Native objects and proved suppliers replace application provenance and redundant premises.
-/

@[expose] public section


noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u v

namespace AlgebraicGeometry.Etale.PointShrinking
variable {P X Y : Scheme.{u}} (p : P ⟶ X) (f : X ⟶ Y) (q : P ⟶ Y)
  (h : p ≫ f = q) [Etale f] [IsClosedImmersion q]

lemma shrinkOpen_eq_top (H : IsPullback p (𝟙 P) f q) : shrinkOpen p f q h = ⊤ := by
  have hs : fiberSection p f q h = H.isoPullback.hom := by
    apply pullback.hom_ext <;> simp
  have hr : Set.range (fiberSection p f q h) = Set.univ := by
    rw [hs]
    exact Set.range_eq_univ.mpr (Scheme.homeoOfIso H.isoPullback).surjective
  ext z
  simp [shrinkOpen, hr]

end AlgebraicGeometry.Etale.PointShrinking
