/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.KrullDimension.Surjective
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Dimension of the actual image of a proper morphism

The original morphism to its schematic image is proper and surjective, so
specialization-chain lifting bounds the image dimension by the source
dimension. The result does not assert that finite maps preserve the dimension
of an unrelated target or that a pointwise Abel bijection is birational.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A proper surjection bounds the dimension of its actual target by that
of its source. No integrality or Noetherianity is needed. -/
theorem topologicalKrullDim_le_of_isProper_of_surjective
    [IsProper f] [Surjective f] : topologicalKrullDim Y ≤ topologicalKrullDim X :=
  TopologicalSpace.topologicalKrullDim_le_of_isClosedMap_of_surjective f f.continuous
    f.isClosedMap f.surjective

/-- The factorization of a proper map through its actual schematic image
is proper. -/
theorem isProper_toImage [IsProper f] : IsProper f.toImage := by
  have : IsProper (f.toImage ≫ f.imageι) := by
    rw [f.toImage_imageι]
    infer_instance
  exact IsProper.of_comp f.toImage f.imageι

/-- The same proper image factorization is surjective, using its actual
dense image and its closed-map property. -/
theorem surjective_toImage_of_isProper [IsProper f] : Surjective f.toImage := by
  have := isProper_toImage f
  exact ⟨Set.range_eq_univ.mp
    (f.toImage.isClosedMap.isClosed_range.closure_eq.symm.trans
      f.toImage.denseRange.closure_range)⟩

/-- A proper schematic image has dimension at most that of the actual
parameter scheme. In particular this applies to proper Abel morphisms. -/
theorem topologicalKrullDim_image_le [IsProper f] :
    topologicalKrullDim f.image ≤ topologicalKrullDim X := by
  have := isProper_toImage f
  have := surjective_toImage_of_isProper f
  exact topologicalKrullDim_le_of_isProper_of_surjective f.toImage

end AlgebraicGeometry.Scheme.Hom
