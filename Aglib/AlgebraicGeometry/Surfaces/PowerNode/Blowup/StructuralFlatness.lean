/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Resolution.SourceGeometry
public import Aglib.AlgebraicGeometry.Morphisms.Flat.GenericFiberCriteria

/-!
Native extraction from the R5 local-model source
`PointedResolution.Blowup.StructuralFlatness`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`ca091719a3daed3b6c80b5efcfc62c2e94e01d275e00cbad2b76c9095fa475fc`.
Original objects, maps, quantifiers and mathematical hypotheses are retained.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

/-!
# Structural flatness of the actual one-step node blowup from its three affine charts.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
universe u

section NodeBlowupStructuralFlatness


/-!
# Structural flatness of the actual one-step node blowup

The structure morphism of any selected ordinary node blowup is flat over the
original DVR. The proof uses exactly its actual three-chart affine open cover,
with the existing structural ring maps. No flatness field or new universal
family is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
namespace AlgebraicGeometry.Scheme.PowerNode.OneStepBlowup
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {π : R} {m : ℕ} (D : Data π m) (hπ : Irreducible π)

@[reassoc] lemma leftChartMap_base_triangle :
    leftChartMap D.atlas hπ ≫ D.blowup.map ≫ Resolution.base =
      Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π))) := by
  rw [BlowupAtlas.leftChartMap_triangle_assoc]
  exact AlgebraicGeometry.Spec.map_algHom_algebraMap (leftBase π m)

@[reassoc] lemma middleChartMap_base_triangle :
    middleChartMap D.atlas hπ ≫ D.blowup.map ≫ Resolution.base =
      Resolution.base (π := π) (n := m) := by
  rw [BlowupAtlas.middleChartMap_triangle_assoc]
  exact AlgebraicGeometry.Spec.map_algHom_algebraMap (middleBase π m)

@[reassoc] lemma rightChartMap_base_triangle :
    rightChartMap D.atlas hπ ≫ D.blowup.map ≫ Resolution.base =
      Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π))) := by
  rw [BlowupAtlas.rightChartMap_triangle_assoc]
  exact AlgebraicGeometry.Spec.map_algHom_algebraMap (rightBase π m)

/-- Flatness over the original DVR, derived from all three actual blowup charts. -/
theorem structural_flat (hπ : Irreducible π) :
    Flat (D.blowup.map ≫ Resolution.base (π := π) (n := m + 2)) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Flat)
    (affineOpenCover D hπ).openCover).mpr
  intro i
  change Fin 3 at i
  fin_cases i
  · change Flat (leftChartMap D.atlas hπ ≫ D.blowup.map ≫ Resolution.base)
    rw [leftChartMap_base_triangle, Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (Resolution.uniformizerNode_flat hπ)
  · change Flat (middleChartMap D.atlas hπ ≫ D.blowup.map ≫ Resolution.base)
    rw [middleChartMap_base_triangle]
    exact Resolution.base_flat hπ.ne_zero
  · change Flat (rightChartMap D.atlas hπ ≫ D.blowup.map ≫ Resolution.base)
    rw [rightChartMap_base_triangle, Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (Resolution.uniformizerNode_flat hπ)

end AlgebraicGeometry.Scheme.PowerNode.OneStepBlowup

end
end NodeBlowupStructuralFlatness
