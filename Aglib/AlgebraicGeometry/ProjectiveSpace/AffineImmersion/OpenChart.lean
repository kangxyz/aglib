/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.AffineImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Closed projective-chart embeddings of actual affine opens

The original finite-type structural map on an affine open is presented by a
closed immersion into the distinguished affine chart of a finite polynomial
projective space. The chart, closedness and original structural equation are
retained together for the target-local Chow construction.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] {X : Scheme.{u}}

/-- An actual affine open of a locally finite-type scheme is closed in an
actual distinguished projective chart, over its original structural map. -/
theorem exists_projectiveChart_closedImmersion_of_isAffineOpen
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (I : Type u) (_ : Fintype I)
      (j : U.toScheme ⟶ (coordinateOpen R (Option I) none).toScheme),
      IsClosedImmersion j ∧
        (j ≫ (coordinateOpen R (Option I) none).ι) ≫ toSpec R (Option I) = U.ι ≫ f := by
  let φ : CommRingCat.of R ⟶ Γ(X, U) := Spec.preimage (hU.isoSpec.inv ≫ U.ι ≫ f)
  have hφ : φ.hom.FiniteType := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    dsimp only [φ]
    rw [Spec.map_preimage]
    infer_instance
  obtain ⟨I, hI, j, hj, hcomp⟩ :=
    exists_projectiveChart_closedImmersion_of_finiteType (R := R) (A := Γ(X, U)) φ.hom hφ
  let := hI
  let := hj
  refine ⟨I, hI, hU.isoSpec.hom ≫ j, inferInstance, ?_⟩
  calc
    ((hU.isoSpec.hom ≫ j) ≫ (coordinateOpen R (Option I) none).ι) ≫
        toSpec R (Option I) =
        hU.isoSpec.hom ≫ ((j ≫ (coordinateOpen R (Option I) none).ι) ≫
          toSpec R (Option I)) := by simp only [Category.assoc]
    _ = hU.isoSpec.hom ≫ Spec.map φ := by rw [hcomp]; rfl
    _ = U.ι ≫ f := by
      dsimp only [φ]
      rw [Spec.map_preimage]
      simp

end AlgebraicGeometry.ProjectiveSpace
