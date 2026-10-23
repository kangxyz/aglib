/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.PointCoordinates

/-!
# Actual points of the original finite product of native projective lines

The existing finite native over-product assembles the original normalized
factor morphisms. The original component projections recover them exactly,
and every relative field-valued point is one of these same product morphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Field

universe u

variable {R K : Type u} [CommRing R] [Field K] {n : ℕ}

/-- The original normalized factor morphisms regarded over their original base. -/
def factorPoint (β : R →+* K) (a : Fin n → Option K) (i : Fin n) :
    Over.mk (Spec.map (CommRingCat.ofHom β)) ⟶ factor R n i :=
  Over.homMk (linePoint β (a i)) (linePoint_over β (a i))

/-- The original field-valued point of the existing finite product. -/
def sourcePoint (β : R →+* K) (a : Fin n → Option K) : Spec (.of K) ⟶ source R n :=
  (Scheme.finiteProductOverLift (factor R n) (factorPoint β a)).left

@[reassoc (attr := simp)]
theorem sourcePoint_over (β : R →+* K) (a : Fin n → Option K) :
    sourcePoint β a ≫ structureMap R n = Spec.map (CommRingCat.ofHom β) :=
  (Scheme.finiteProductOverLift (factor R n) (factorPoint β a)).w

@[reassoc (attr := simp)]
theorem sourcePoint_projection (β : R →+* K) (a : Fin n → Option K) (i : Fin n) :
    sourcePoint β a ≫ projection R n i = linePoint β (a i) :=
  congrArg (fun h => h.left)
    (Scheme.finiteProductOverLift_π (factor R n) (factorPoint β a) i)

-- The fundamental projection and line-chart rules supply simp normalization.
@[reassoc]
theorem sourcePoint_liftedProjection (β : R →+* K) (a : Fin n → Option K) (i : Fin n) :
    sourcePoint β a ≫ liftedProjection R n i = liftedLinePoint β (a i) := by
  rw [← Category.assoc, sourcePoint_projection, linePoint_lifted]

/-- Every actual relative point of the original finite product is recovered
from its actual normalized factor coordinates. -/
theorem exists_sourcePoint (β : R →+* K) (s : Spec (.of K) ⟶ source R n)
    (hs : s ≫ structureMap R n = Spec.map (CommRingCat.ofHom β)) :
    ∃ a : Fin n → Option K, sourcePoint β a = s := by
  have h (i : Fin n) : ∃ a : Option K, linePoint β a = s ≫ projection R n i := by
    apply exists_linePoint
    rw [Category.assoc, projection_over, hs]
  choose a ha using h
  refine ⟨a, ?_⟩
  let f : Over.mk (Spec.map (CommRingCat.ofHom β)) ⟶ product R n :=
    Over.homMk (sourcePoint β a) (sourcePoint_over β a)
  let g : Over.mk (Spec.map (CommRingCat.ofHom β)) ⟶ product R n := Over.homMk s hs
  have he : f = g := by
    apply Scheme.finiteProductOver_hom_ext (factor R n)
    intro i
    apply Over.OverMorphism.ext
    exact (sourcePoint_projection β a i).trans (ha i)
  exact congrArg (fun h => h.left) he

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Field
