/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.AffineImmersion
public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective

/-!
# Affine schemes of finite type are quasi-projective

For a ring map `φ : R →+* A` of finite type, `Spec A ⟶ Spec R` is H-quasi-projective
(`isHQuasiProjective_spec_map_of_finiteType`): `A` is a quotient of a polynomial ring in finitely
many variables, so `Spec A` is a closed subscheme of the standard affine chart `D₊(X_none)` of
projective space with coordinates `Option I`
(`ProjectiveSpace.exists_projectiveImmersion_of_finiteType`), and this immersion is quasi-compact
because `Spec A` is quasi-compact and projective space is separated. The definition of
H-quasi-projective is Stacks, Definition 29.41.1 (Tag 01VW), over the affine base `Spec R`
(`Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **Affine schemes of finite type are H-quasi-projective**: for a ring map `φ : R →+* A` of
finite type, `Spec A ⟶ Spec R` factors as a quasi-compact immersion into projective space over
`Spec R`. -/
theorem isHQuasiProjective_spec_map_of_finiteType {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) (hφ : φ.FiniteType) : IsHQuasiProjective (Spec.map (CommRingCat.ofHom φ)) := by
  obtain ⟨I, _, j, hj, h⟩ := ProjectiveSpace.exists_projectiveImmersion_of_finiteType φ hφ
  exact ⟨Option I, inferInstance, j, hj, inferInstance, h⟩

end AlgebraicGeometry
