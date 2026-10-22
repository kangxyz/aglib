/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Basic
public import Aglib.AlgebraicGeometry.ProjectiveSpace.AffineImmersion

/-!
# Compactification of finite-type affine morphisms

For any finite-type ring map, embed its spectrum into finite polynomial projective
space and take the native scheme-theoretic image. This yields a dense open immersion
followed by a proper morphism, with exactly the original Spec map as composite.
The rings are arbitrary commutative rings, not necessarily Noetherian.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {R A : Type u} [CommRing R] [CommRing A]

/-- Every finite-type map of arbitrary commutative rings has a compactification of its
actual spectrum morphism, with dense open source. No Noetherian assumption is required. -/
theorem exists_compactification_of_finiteType (φ : R →+* A) (hφ : φ.FiniteType) :
    ∃ C : Compactification (Spec.map (CommRingCat.ofHom φ)), IsDominant C.j := by
  obtain ⟨I, hI, j, hj, hcomp⟩ :=
    ProjectiveSpace.exists_projectiveImmersion_of_finiteType φ hφ
  let := hI
  let := hj
  have : QuasiCompact (j ≫ ProjectiveSpace.toSpec R (Option I)) := by
    rw [hcomp]
    infer_instance
  have : QuasiCompact j := QuasiCompact.of_comp j (ProjectiveSpace.toSpec R (Option I))
  exact exists_compactification_of_immersion _ j (ProjectiveSpace.toSpec R (Option I)) hcomp

end AlgebraicGeometry.Scheme.Hom
