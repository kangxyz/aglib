/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAffineModule

/-! # Original scalar towers of formal graded affine modules -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite DirectSum GradedMonoid
open scoped TensorProduct
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I)) (U : X.Opens)

/-- The graded-piece sections retain the original structural base-ring action. -/
local instance (n : ℕ) : Module A Γ(F.gradedPiece n, U) :=
  idealSectionModule X (idealThickeningBaseScalar f) (F.gradedPiece n) U
local instance (n : ℕ) :
    letI := formalGradedSectionAlgebra f U
    IsScalarTower A Γ(X, U) Γ(F.gradedPiece n, U) := by
  let := formalGradedSectionAlgebra f U
  exact IsScalarTower.of_compHom A Γ(X, U) Γ(F.gradedPiece n, U)
/-- Homogeneous scalars act through the original maps between graded-piece sections. -/
local instance : DirectSum.Gmodule (fun n => I.associatedGradedGrading n)
    (fun n => Γ(F.gradedPiece n, U)) := formalGradedSectionsGModule f I F U
/-- The actual graded section total carries its external associated-graded action. -/
local instance : Module I.associatedGraded (⨁ n, Γ(F.gradedPiece n, U)) :=
  formalGradedExternalSectionsModule f I F U
local instance : SMulCommClass Γ(X, U) I.associatedGraded (⨁ n, Γ(F.gradedPiece n, U)) :=
  formalGradedExternalSectionsComm f I F U
local instance : IsScalarTower A I.associatedGraded (⨁ n, Γ(F.gradedPiece n, U)) :=
  formalGradedExternalSectionsTower f I F U
/-- The original coordinate and graded scalar actions combine into the tensor action. -/
local instance :
    letI := formalGradedSectionAlgebra f U
    Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) := by
  letI := formalGradedSectionAlgebra f U
  exact formalGradedAffineModule f I F U
local instance :
    letI := formalGradedSectionAlgebra f U
    IsScalarTower Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded)
    (⨁ n, Γ(F.gradedPiece n, U)) := by
  let := formalGradedSectionAlgebra f U
  exact Algebra.TensorProduct.commutingModule_scalarTower_left A Γ(X, U) I.associatedGraded _

/-- Forgetting the tensor action recovers the original coordinate-ring action. -/
theorem formalGradedAffineModule_scalarTower_left :
    letI := formalGradedSectionAlgebra f U
    letI := formalGradedAffineModule f I F U
    IsScalarTower Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, U)) := by
  let := formalGradedSectionAlgebra f U
  let := formalGradedAffineModule f I F U
  exact Algebra.TensorProduct.commutingModule_scalarTower_left A Γ(X, U) I.associatedGraded _

/-- Every tensor of a homogeneous scalar acts by the original homogeneous sheaf map. -/
theorem formalGradedAffineModule_tmul_component_smul (b : Γ(X, U)) (r n : ℕ)
    (a : I.associatedGradedGrading r) (x : Γ(F.gradedPiece n, U)) :
    letI := formalGradedSectionAlgebra f U
    letI := formalGradedAffineModule f I F U
    (b ⊗ₜ[A] (a : I.associatedGraded)) • DirectSum.of (fun k => Γ(F.gradedPiece k, U)) n x =
      DirectSum.of (fun k => Γ(F.gradedPiece k, U)) (r + n)
        (b • (formalGradedHomogeneousAction f I F r n a).app U x) := by
  let := formalGradedSectionAlgebra f U
  let := formalGradedAffineModule f I F U
  change b • ((a : I.associatedGraded) •
    DirectSum.of (fun k => Γ(F.gradedPiece k, U)) n x) = _
  rw [I.associatedGradedExternalModule_smul, ← DirectSum.of_smul]
  rfl

end AlgebraicGeometry.Scheme.Cohomology
