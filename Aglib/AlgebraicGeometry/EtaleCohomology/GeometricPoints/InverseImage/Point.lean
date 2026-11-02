/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage.Skyscraper
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import Mathlib.CategoryTheory.Sites.Point.Category

/-! # The original geometric point as the native site comap point -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

variable {X S : Scheme.{u}} (f : S ⟶ X)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S)

/-- The original geometric point bijection as an isomorphism of fibre functors. -/
def geometricPointComapFiberIso :
    (pointSmallEtale (η ≫ f)).fiber ≅ siteBaseChange f ⋙ (pointSmallEtale η).fiber :=
  NatIso.ofComponents (fun U => (StalkInverseImage.pointEquiv f η U).toIso)
    (by
      intro U V g
      ext p
      exact StalkInverseImage.pointEquiv_naturality f η g p)

/-- Smallness of the actual comap point follows from the original geometric point. -/
theorem geometricPointComap_initiallySmall :
    InitiallySmall.{u} (siteBaseChange f ⋙ (pointSmallEtale η).fiber).Elements := by
  let e := (Functor.Elements.structuredArrowEquivalence
      (pointSmallEtale (η ≫ f)).fiber).trans
    ((StructuredArrow.mapNatIso (geometricPointComapFiberIso f η)).trans
      (Functor.Elements.structuredArrowEquivalence
        (siteBaseChange f ⋙ (pointSmallEtale η).fiber)).symm)
  exact initiallySmall_of_initial_of_initiallySmall e.functor

attribute [local instance] geometricPointComap_initiallySmall

local instance geometricPointComapRepresentablyFlat : RepresentablyFlat (siteBaseChange f) :=
  flat_of_preservesFiniteLimits (siteBaseChange f)

/-- The original geometric point identifies with the native site comap point. -/
def geometricPointComapIso :
    pointSmallEtale (η ≫ f) ≅
      (pointSmallEtale η).comap (siteBaseChange f) (siteBaseChange_coverPreserving f) where
  hom := ⟨(geometricPointComapFiberIso f η).inv⟩
  inv := ⟨(geometricPointComapFiberIso f η).hom⟩
  hom_inv_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (geometricPointComapFiberIso f η).hom_inv_id
  inv_hom_id := by
    apply GrothendieckTopology.Point.hom_ext
    exact (geometricPointComapFiberIso f η).inv_hom_id

end AlgebraicGeometry.Scheme.EtaleCohomology
