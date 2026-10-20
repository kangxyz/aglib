/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Nodal.Polygon.Gluing

/-!
# The original structural projection of the unmarked polygon

Source: frozen R5 `Curves/Cyclic/Covers/FiniteCover.lean`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`.
The original actual schemes, kernel ideals and structural triangles are retained.
Unused model wrappers are replaced by the actual scheme and map parameters.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u
namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

/-- The affine projection from the polygon node scheme to the pinched affine line. -/
def affineMap : nodeScheme k n ⟶ Scheme.PinchedLine.nodeScheme k :=
  Spec.map (CommRingCat.ofHom (baseMap k n).toRingHom)

/-- The affine polygon projection is finite. -/
instance affineMap_finite : IsFinite (affineMap k n) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr (finiteModule k n)

theorem affineMap_surjective [NeZero n] : Function.Surjective (affineMap k n) :=
  RingHom.IsIntegral.comap_surjective
    (RingHom.finite_algebraMap.mpr (finiteModule k n)).to_isIntegral
    (baseMap_injective k n)
/-- The projection from the product overlap chart to the pinched-line overlap. -/
def overlapMap : overlapScheme k n ⟶ Spec (.of (W k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (W k) (productOverlapRing k n)))

/-- The projection from the product infinity chart to the pinched-line infinity chart. -/
def infinityMap : infinityScheme k n ⟶ Spec (.of (V k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (V k) (productInfinityRing k n)))
theorem affine_compatibility : gluingToNode k n ≫ affineMap k n =
    overlapMap k n ≫ Scheme.PinchedLine.gluingToNode k := by
  rw [gluingToNode_spec, Scheme.PinchedLine.gluingToNode_spec]
  unfold affineMap overlapMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem infinity_compatibility : gluingToInfinity k n ≫ infinityMap k n =
    overlapMap k n ≫ Scheme.PinchedLine.gluingToInfinity k := by
  rw [gluingToInfinity_spec, Scheme.PinchedLine.gluingToInfinity_spec]
  unfold infinityMap overlapMap
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- The literal global n-cycle map, retaining the same actual affine cover. -/
def cycleMap : cycleScheme k n ⟶ Scheme.PinchedLine.pinchedGluing k :=
  pushout.desc
    (affineMap k n ≫ pushout.inl (Scheme.PinchedLine.gluingToNode k)
      (Scheme.PinchedLine.gluingToInfinity k))
    (infinityMap k n ≫ pushout.inr (Scheme.PinchedLine.gluingToNode k)
      (Scheme.PinchedLine.gluingToInfinity k))
    (by
      rw [← Category.assoc, affine_compatibility, Category.assoc, pushout.condition,
        ← Category.assoc, ← infinity_compatibility, Category.assoc])

@[simp] theorem cycleMap_affine :
    pushout.inl (gluingToNode k n) (gluingToInfinity k n) ≫ cycleMap k n =
      affineMap k n ≫ pushout.inl (Scheme.PinchedLine.gluingToNode k)
        (Scheme.PinchedLine.gluingToInfinity k) :=
  pushout.inl_desc _ _ _

@[simp] theorem cycleMap_infinity :
    pushout.inr (gluingToNode k n) (gluingToInfinity k n) ≫ cycleMap k n =
      infinityMap k n ≫ pushout.inr (Scheme.PinchedLine.gluingToNode k)
        (Scheme.PinchedLine.gluingToInfinity k) :=
  pushout.inr_desc _ _ _
/-- Actual k-structure through the proved finite map to the proper one-gon. -/
def structureMap : cycleScheme k n ⟶ Spec (.of k) :=
  cycleMap k n ≫ Scheme.PinchedLine.pinchedStructure k

end AlgebraicGeometry.Scheme.Polygon
