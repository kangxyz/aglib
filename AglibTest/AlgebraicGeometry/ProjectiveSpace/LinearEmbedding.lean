/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.LinearEmbedding

/-!
# Linear closed immersions of projective spaces

The declarations below restate the linear embedding `P(ι)_R ⟶ P(κ)_R` of an injective map of
coordinate types as a closed immersion over `Spec R`, specialize it to the standard inclusion
`P^n_R ⊆ P^m_R` for `n ≤ m`, and guard their axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AglibTest.LinearEmbedding

/-- The linear embedding of an injective map of coordinate types is a closed immersion over
`Spec R`, and its graded ring map is surjective in every degree. -/
theorem linearEmbedding (R : Type u) [CommRing R] {ι κ : Type u} {j : ι → κ}
    (hj : Function.Injective j) :
    IsClosedImmersion (ProjectiveSpace.linearEmbedding R hj) ∧
      ProjectiveSpace.linearEmbedding R hj ≫ ProjectiveSpace.toSpec R κ =
        ProjectiveSpace.toSpec R ι ∧
      ∀ n, Function.Surjective ((MvPolynomial.gradedKillCompl R hj).gradedAddHom n) :=
  ⟨inferInstance, ProjectiveSpace.linearEmbedding_toSpec R hj,
    MvPolynomial.gradedKillCompl_degreewise_surjective R hj⟩

/-- The standard linear subspace `P^n_R ⊆ P^m_R` for `n ≤ m`, through `Fin.castLE`. -/
theorem standard (R : Type u) [CommRing R] {n m : ℕ} (h : n + 1 ≤ m + 1) :
    IsClosedImmersion (ProjectiveSpace.linearEmbedding R
      (ULift.up_injective.comp ((Fin.castLE_injective h).comp ULift.down_injective) :
        Function.Injective fun i : ULift.{u} (Fin (n + 1)) => ULift.up (Fin.castLE h i.down))) :=
  inferInstance

/-- info: 'AglibTest.LinearEmbedding.linearEmbedding' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.LinearEmbedding.linearEmbedding

/-- info: 'AglibTest.LinearEmbedding.standard' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.LinearEmbedding.standard

end AglibTest.LinearEmbedding
