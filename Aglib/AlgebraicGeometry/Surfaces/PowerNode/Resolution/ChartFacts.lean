/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.Range
public import Aglib.AlgebraicGeometry.Blowup.BasicOpenIsomorphism
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Resolution.Data

/-!
Native extraction from the R5 local-model source
`PointedResolution.Resolution.ChartFacts`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`3e499136675e90da5efe793f16ae68900ddac2f3cada8a68f7d8235d0157a579`.
Original objects, maps, quantifiers and mathematical hypotheses are retained.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

/-!
# Restriction and outer-chart facts for the actual recursive node resolution.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre
universe u

section NodeResolutionChartFacts


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.Blowup.Coordinates
  AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas AlgebraicGeometry.Scheme.PowerNode.BlowupOverlaps
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution


variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {π : R} {m : ℕ} (D : OneStepBlowup.Data π m) (hπ : Irreducible π)

/-- The union of the left and right chart images in the chosen one-step node blowup. -/
def outerOpen : D.blowup.Y.Opens :=
  (leftChartMap D.atlas hπ).opensRange ⊔ (rightChartMap D.atlas hπ).opensRange

lemma middle_preimage_outer : middleChartMap D.atlas hπ ⁻¹ᵁ outerOpen D hπ =
    uOpen π m ⊔ vOpen π m := by
  have hu := preimage_range_of_overlap (awayMap (PlaneNode.U (π^m)))
    (middleChartMap D.atlas hπ) (leftChartMap D.atlas hπ)
    (overlap_range D.atlas (generator π m 1) (generator π m 0)
      (dvrMiddleReesEquiv π hπ m).toRingEquiv (dvrLeftReesEquiv π hπ m).toRingEquiv
      (PlaneNode.U (π^m)) (middle_left_ratio π hπ m))
  have hv := preimage_range_of_overlap (awayMap (PlaneNode.V (π^m)))
    (middleChartMap D.atlas hπ) (rightChartMap D.atlas hπ)
    (overlap_range D.atlas (generator π m 1) (generator π m 2)
      (dvrMiddleReesEquiv π hπ m).toRingEquiv (dvrRightReesEquiv π hπ m).toRingEquiv
      (PlaneNode.V (π^m)) (middle_right_ratio π hπ m))
  have hu' : Set.range (awayMap (PlaneNode.U (π^m))) = (uOpen π m : Set (X π m)) :=
    PrimeSpectrum.localization_away_comap_range _ _
  have hv' : Set.range (awayMap (PlaneNode.V (π^m))) = (vOpen π m : Set (X π m)) :=
    PrimeSpectrum.localization_away_comap_range _ _
  apply TopologicalSpace.Opens.ext
  change (middleChartMap D.atlas hπ) ⁻¹' (_ ∪ _) = _ ∪ _
  rw [Set.preimage_union]
  change (middleChartMap D.atlas hπ) ⁻¹' Set.range (leftChartMap D.atlas hπ) ∪
    (middleChartMap D.atlas hπ) ⁻¹' Set.range (rightChartMap D.atlas hπ) = _
  rw [hu, hv, hu', hv']

lemma middle_outer_cover :
    (middleChartMap D.atlas hπ).opensRange ⊔ outerOpen D hπ = ⊤ := by
  apply top_le_iff.mp
  intro x _
  rcases three_charts_cover D.atlas hπ x with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

lemma outer_regular : RegularStalks (outerOpen D hπ).toScheme := by
  intro x
  have hx : IsRegularLocalRing (D.blowup.Y.presheaf.stalk ((outerOpen D hπ).ι x)) := by
    change IsRegularLocalRing (D.blowup.Y.presheaf.stalk x.val)
    rcases x.property with ⟨y, hy⟩ | ⟨y, hy⟩
    · rw [← hy]
      exact Scheme.RegularStalks.at_image (leftChartMap D.atlas hπ)
        (PlaneNode.Regularity.uniformizerNode_stalk_regular π hπ) y
    · rw [← hy]
      exact Scheme.RegularStalks.at_image (rightChartMap D.atlas hπ)
        (PlaneNode.Regularity.uniformizerNode_stalk_regular π hπ) y
  exact IsRegularLocalRing.of_ringEquiv
    (asIso ((outerOpen D hπ).ι.stalkMap x)).commRingCatIsoToRingEquiv

lemma blowup_preimage_u_le_outer : D.blowup.map ⁻¹ᵁ uOpen π (m + 2) ≤ outerOpen D hπ := by
  intro x hx
  left
  change x ∈ Set.range (leftChartMap D.atlas hπ)
  rw [leftChartMap, AlgebraicGeometry.Scheme.Hom.Range.range_iso_comp]
  have hx' : x ∈ Set.range (AlgebraicGeometry.Scheme.Blowup.UnitLocus.unitChartMap D.atlas
    (generator π m 0)) := by
    rw [AlgebraicGeometry.Scheme.Blowup.UnitLocus.unitChartMap_range]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  exact ⟨_, rfl⟩

lemma blowup_preimage_v_le_outer : D.blowup.map ⁻¹ᵁ vOpen π (m + 2) ≤ outerOpen D hπ := by
  intro x hx
  right
  change x ∈ Set.range (rightChartMap D.atlas hπ)
  rw [rightChartMap, AlgebraicGeometry.Scheme.Hom.Range.range_iso_comp]
  have hx' : x ∈ Set.range (AlgebraicGeometry.Scheme.Blowup.UnitLocus.unitChartMap D.atlas
    (generator π m 2)) := by
    rw [AlgebraicGeometry.Scheme.Blowup.UnitLocus.unitChartMap_range]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  exact ⟨_, rfl⟩

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma blowup_u_isIso : IsIso (D.blowup.map ∣_ uOpen π (m + 2)) :=
  blowup_restrict_isIso D.atlas (generator π m 0)
omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma blowup_v_isIso : IsIso (D.blowup.map ∣_ vOpen π (m + 2)) :=
  blowup_restrict_isIso D.atlas (generator π m 2)

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end
end NodeResolutionChartFacts
