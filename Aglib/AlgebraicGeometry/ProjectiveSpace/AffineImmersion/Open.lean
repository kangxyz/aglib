/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.AffineImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Projective immersions of actual affine opens over an affine base

The finite-type polynomial presentation theorem is transported through the
original affine-open Spec isomorphism. Its structural factorization is the
original morphism restricted to that open, not a chosen alternative ring action.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] {X : Scheme.{u}}

/-- Every affine open of a locally finite-type scheme over `Spec R` immerses into a
finite polynomial projective space with its original structural map. -/
theorem exists_projectiveImmersion_of_isAffineOpen
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (I : Type u) (_ : Fintype I) (j : U.toScheme ⟶ ProjectiveSpace R (Option I)),
      IsImmersion j ∧ j ≫ toSpec R (Option I) = U.ι ≫ f := by
  let φ : CommRingCat.of R ⟶ Γ(X, U) := Spec.preimage (hU.isoSpec.inv ≫ U.ι ≫ f)
  have hφ : φ.hom.FiniteType := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    dsimp only [φ]
    rw [Spec.map_preimage]
    infer_instance
  obtain ⟨I, hI, j, hj, hcomp⟩ :=
    exists_projectiveImmersion_of_finiteType (R := R) (A := Γ(X, U)) φ.hom hφ
  let := hI
  let := hj
  refine ⟨I, hI, hU.isoSpec.hom ≫ j, inferInstance, ?_⟩
  rw [Category.assoc, hcomp]
  change hU.isoSpec.hom ≫ Spec.map φ = U.ι ≫ f
  dsimp only [φ]
  rw [Spec.map_preimage]
  simp

end AlgebraicGeometry.ProjectiveSpace
