/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalPoint.ClosedLift
public import Aglib.AlgebraicGeometry.RationalPoint.SurjectiveLift
public import Aglib.AlgebraicGeometry.Dimension.ProperImage

/-!
# Geometric points of the original proper schematic image

A field-valued point in the original closed image lifts through its actual
closed immersion because the field is reduced. The original proper map
to that image is surjective: its dense range is closed. The existing
locally finite type geometric-point lifting theorem then supplies a lift
through the original source. Both original factorization maps are retained.

The source may be empty. No integrality, flatness, projectivity or fibre
cardinality premise is imposed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An actual geometric point of the proper schematic image lifts through
the original source and both original image-factorization triangles. -/
theorem exists_lift_toImage_of_mem_image (K : Type u) [Field K] [IsAlgClosed K]
    (t : Spec (.of K) ⟶ Y) (ht : t (IsLocalRing.closedPoint K) ∈ Set.range f.imageι) :
    ∃ (u : Spec (.of K) ⟶ X) (v : Spec (.of K) ⟶ f.image),
      u ≫ f.toImage = v ∧ v ≫ f.imageι = t := by
  have := isProper_toImage f
  have := surjective_toImage_of_isProper f
  obtain ⟨v, hv⟩ := RationalPoint.closedImmersion_fieldPoint_lift f.imageι K t (by
    simpa only [show (default : Spec (.of K)) = IsLocalRing.closedPoint K from
      Subsingleton.elim _ _] using ht)
  obtain ⟨u, hu⟩ := f.toImage.exists_lift_spec_of_isAlgClosed K v
  exact ⟨u, v, hu, hv⟩

/-- Membership in the actual schematic image of a proper morphism is
equivalent to a literal lift of the specified algebraically closed field test. -/
theorem mem_image_iff_exists_lift_spec (K : Type u) [Field K] [IsAlgClosed K]
    (t : Spec (.of K) ⟶ Y) :
    t (IsLocalRing.closedPoint K) ∈ Set.range f.imageι ↔
      ∃ u : Spec (.of K) ⟶ X, u ≫ f = t := by
  constructor
  · intro ht
    obtain ⟨u, v, hu, hv⟩ := exists_lift_toImage_of_mem_image f K t ht
    refine ⟨u, ?_⟩
    rw [← f.toImage_imageι, ← Category.assoc, hu, hv]
  · rintro ⟨u, hu⟩
    refine ⟨f.toImage (u (IsLocalRing.closedPoint K)), ?_⟩
    change (u ≫ f.toImage ≫ f.imageι) (IsLocalRing.closedPoint K) = t (IsLocalRing.closedPoint K)
    rw [f.toImage_imageι, hu]

end AlgebraicGeometry.Scheme.Hom
