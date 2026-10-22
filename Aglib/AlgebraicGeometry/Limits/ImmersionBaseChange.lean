/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.Range
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Closed ranges of the original base-changed immersion

These criteria concern the actual `Over.pullback` map and the actual
diagonal of a pullback projection. They require no flatness or finiteness.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- Closed inverse images under the two symmetric native pullback projections agree. -/
theorem isClosed_preimage_pullback_swap {Y S T : Scheme.{u}}
    (g : Y ⟶ S) (b : T ⟶ S) (Z : Set Y) :
    IsClosed (pullback.fst g b ⁻¹' Z) ↔ IsClosed (pullback.snd b g ⁻¹' Z) := by
  constructor
  · intro h
    have H := h.preimage (pullbackSymmetry b g).hom.continuous
    simpa only [← Set.preimage_comp, ← TopCat.coe_comp, ← Hom.comp_base,
      pullbackSymmetry_hom_comp_fst] using H
  · intro h
    have H := h.preimage (pullbackSymmetry g b).hom.continuous
    simpa only [← Set.preimage_comp, ← TopCat.coe_comp, ← Hom.comp_base,
      pullbackSymmetry_hom_comp_snd] using H

/-- The original over-category base-change map has the expected cartesian square. -/
theorem isPullback_overPullbackMap {S T : Scheme.{u}} (b : T ⟶ S)
    {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (pullback.fst X.hom b) ((Over.pullback b).map f).left
      f.left (pullback.fst Y.hom b) := by
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback Y.hom b)
  · simpa only [Over.pullback_map_left, pullback.lift_snd, Over.w] using
      (IsPullback.of_hasPullback X.hom b)
  · simp only [Over.pullback_map_left, pullback.lift_fst]

/-- The native base change of an immersion is closed precisely when the
original range has closed inverse image under the target projection. -/
theorem isClosedImmersion_overPullbackMap_iff {S T : Scheme.{u}} (b : T ⟶ S)
    {X Y : Over S} (f : X ⟶ Y) [IsImmersion f.left] :
    IsClosedImmersion ((Over.pullback b).map f).left ↔
      IsClosed (pullback.fst Y.hom b ⁻¹' Set.range f.left) := by
  let q : pullback X.hom b ⟶ pullback Y.hom b := ((Over.pullback b).map f).left
  have : IsImmersion q :=
    MorphismProperty.overPullbackMap (P := @IsImmersion) b f inferInstance
  have H : IsPullback (pullback.fst X.hom b) q f.left (pullback.fst Y.hom b) :=
    isPullback_overPullbackMap b f
  have hrange : Set.range q = pullback.fst Y.hom b ⁻¹' Set.range f.left :=
    Pullback.Fibre.pullback_range_snd H
  change IsClosedImmersion q ↔ IsClosed (pullback.fst Y.hom b ⁻¹' Set.range f.left)
  rw [← hrange]
  exact ⟨fun _ => q.isClosedEmbedding.isClosed_range,
    fun h => IsClosedImmersion.of_isPreimmersion _ h⟩

/-- Separatedness of the original base-changed morphism is closedness of
the inverse image of the original diagonal range. -/
theorem isSeparated_pullback_fst_iff_isClosed_preimage_diagonal
    {X S T : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S) :
    IsSeparated (pullback.fst b f) ↔
      IsClosed (pullback.snd b (pullback.snd f f ≫ f) ⁻¹'
        Set.range (pullback.diagonal f)) := by
  have : IsImmersion ((Over.homMk (pullback.diagonal f) :
      Over.mk f ⟶ Over.mk (pullback.snd f f ≫ f)).left) := by
    change IsImmersion (pullback.diagonal f)
    infer_instance
  rw [AlgebraicGeometry.isSeparated_iff, diagonal_pullback_fst,
    MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion),
    isClosedImmersion_overPullbackMap_iff]
  change IsClosed (pullback.fst (pullback.snd f f ≫ f) b ⁻¹' Set.range (pullback.diagonal f)) ↔ _
  exact isClosed_preimage_pullback_swap (pullback.snd f f ≫ f) b (Set.range (pullback.diagonal f))

end AlgebraicGeometry.Scheme
