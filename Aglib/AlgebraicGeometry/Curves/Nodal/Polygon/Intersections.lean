/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Nodal.Polygon.ComponentGeometry

/-!
# Distinct actual polygon components meet only on the node locus

Source: frozen R5 `Curves/Cyclic/Covers/Components.lean`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`.
The original actual schemes, kernel ideals and structural triangles are retained.
Unused model wrappers are replaced by the actual scheme and map parameters.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
universe u
namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (m : ℕ)

/-- A collision of distinct actual affine polynomial components lies on the
actual conductor. The separating tuple is the conductor supported on one index. -/
theorem affine_component_collision_conductor (i j : Fin m) (hij : i ≠ j)
    (x y : Spec (.of k[X]))
    (h : polynomialCover k m (componentAffine k m i x) =
      polynomialCover k m (componentAffine k m j y)) :
    conductor k m ∈ (polynomialCover k m (componentAffine k m i x)).asIdeal := by
  classical
  let a := conductorMul k m (Pi.single i 1)
  have ha : a ∈ (polynomialCover k m (componentAffine k m j y)).asIdeal := by
    change a.val j ∈ y.asIdeal
    simp [a, conductorMul, Pi.single_eq_of_ne (Ne.symm hij)]
  rw [← h] at ha
  change a.val i ∈ x.asIdeal at ha
  change (conductor k m).val i ∈ x.asIdeal
  simpa [a, conductorMul, conductor] using ha

/-- Distinct actual normalized P1 components can meet only at an actual node. -/
theorem componentLine_collision_node (i j : Fin m) (hij : i ≠ j)
    (x y : Scheme.PinchedLine.lineGluing k)
    (h : gluedPolynomialCover k m (componentLine k m i x) =
      gluedPolynomialCover k m (componentLine k m j y)) :
    gluedPolynomialCover k m (componentLine k m i x) ∈ globalNodeLocus k m := by
  have affine_case (l : Fin m) (a : Spec (.of k[X])) :
      gluedPolynomialCover k m (componentLine k m l
        (pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
            (Scheme.PinchedLine.gluingToInfinity k) a)) =
      pushout.inl (gluingToNode k m) (gluingToInfinity k m)
        (polynomialCover k m (componentAffine k m l a)) := by
    change (pushout.inl _ _ ≫ componentLine k m l ≫ gluedPolynomialCover k m) a = _
    rw [← Category.assoc, componentLine_affine, Category.assoc, gluedPolynomialCover,
      Scheme.OpenNormalizationGluing.affine_chart]
    rfl
  have infinity_case (l r : Fin m) (hlr : l ≠ r) (a : Scheme.PinchedLine.lineGluing k)
      (b : Spec (.of (V k)))
      (hh : gluedPolynomialCover k m (componentLine k m l a) =
        gluedPolynomialCover k m (componentLine k m r
          (pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
              (Scheme.PinchedLine.gluingToInfinity k) b))) : False := by
    have hb := congrArg (fun f : Spec (.of (V k)) ⟶ normalizedScheme k m => f b)
      (componentLine_infinity k m r)
    simp only [Scheme.Hom.comp_apply] at hb
    have he : componentLine k m l a = componentLine k m r
        (pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
            (Scheme.PinchedLine.gluingToInfinity k) b) := by
      rw [hb]
      apply (gluedPolynomialCover_infinity_fibre k m _ _).mp
      exact hh.trans ((gluedPolynomialCover_infinity_fibre k m _ _).mpr hb)
    exact hlr (componentLine_index_eq k m l r _ _ he)
  rcases Scheme.PinchedLine.lineGluing_covered k x with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rcases Scheme.PinchedLine.lineGluing_covered k y with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · have hab := (pushout.inl (gluingToNode k m) (gluingToInfinity k m)).isOpenEmbedding.injective
        ((affine_case i a).symm.trans (h.trans (affine_case j b)))
      rw [affine_case, globalNodeLocus_eq_conductorImage]
      exact ⟨_, affine_component_collision_conductor k m i j hij a b hab, rfl⟩
    · exact (infinity_case i j hij _ b h).elim
  · exact (infinity_case j i hij.symm _ a h.symm).elim

/-- The intersection of two DISTINCT actual irreducible-component images is
contained in the actual conductor node locus. -/
theorem targetComponent_inter_subset_nodes (i j : Fin m) (hij : i ≠ j) :
    targetComponent k m i ∩ targetComponent k m j ⊆ globalNodeLocus k m := by
  rintro z ⟨⟨_, ⟨x, rfl⟩, hx⟩, ⟨_, ⟨y, rfl⟩, hy⟩⟩
  rw [← hx]
  exact componentLine_collision_node k m i j hij x y (hx.trans hy.symm)

end AlgebraicGeometry.Scheme.Polygon
