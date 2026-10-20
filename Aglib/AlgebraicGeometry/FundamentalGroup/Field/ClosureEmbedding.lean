/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.Basic
public import Aglib.RingTheory.RootsOfUnity.FieldPullbackIndependence

/-!
# Geometric points for an explicit compatible closure embedding

The field spectrum map, actual Over arrow, and Galois-equivariance equation are
extracted from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.Kummer.FieldNaturality`
on packet revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. The algebraic-closure
embedding remains an explicit input, and both forward spectrum maps are literal.

The existing native field-embedding module constructs one compatible closure
embedding from an arbitrary field homomorphism. This leaf treats any displayed
compatible embedding for a given field algebra, so it introduces neither a new
choice nor a replacement field fundamental group. It has no H1 dependency.
-/

@[expose] public section

noncomputable section
open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.ClosureEmbedding

open Field.absoluteGaloisGroup.RootsOfUnity

universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  (i : FieldPullbackIndependence.Embedding (K := K) (L := L))

/-- The canonical spectrum map for the given field algebra. -/
abbrev fieldMorphism : Spec (.of L) ⟶ Spec (.of K) := Spec.algebraMap K L

/-- The actual extension of the geometric point along the displayed closure embedding. -/
def pointExtension : Over.mk (geometricPoint L ≫ fieldMorphism (K := K) (L := L)) ⟶
    Over.mk (geometricPoint K) :=
  Over.homMk (Spec.map (CommRingCat.ofHom i.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact i.commutes x)

/-- The point extension uses exactly the displayed closure map. -/
@[simp] theorem pointExtension_left :
    (pointExtension i).left = Spec.map (CommRingCat.ofHom i.toRingHom) := rfl

/-- Actual point precomposition intertwines the genuine Galois restriction. -/
theorem pointExtension_galois (σ : Field.absoluteGaloisGroup L) :
    (Over.map (fieldMorphism (K := K) (L := L))).map (pointEnd L σ) ≫ pointExtension i =
      pointExtension i ≫ pointEnd K (FieldPullbackIndependence.restriction i σ) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  exact (FieldPullbackIndependence.restriction_commutes i σ x).symm

end AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.ClosureEmbedding
