/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAffineFinite

/-! # The original degree-zero presentation on unit tensors -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite DirectSum GradedMonoid
open scoped TensorProduct
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I)) (U : X.Opens)

/-- The actual presentation sends a unit tensor to the original degree-zero inclusion. -/
theorem formalGradedAffinePresentation_one_tmul (m : Γ(F.gradedPiece 0, U)) :
    letI := formalGradedSectionAlgebra f U
    letI : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
    letI : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
      (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
    letI := formalGradedAffineModule f I F U
    letI := formalGradedAffineModule_scalarTower_left f I F U
    formalGradedAffinePresentation f I F U
      ((1 : Γ(X, U) ⊗[A] I.associatedGraded) ⊗ₜ[Γ(X, U)] m) =
      DirectSum.of (fun n => Γ(F.gradedPiece n, U)) 0 m := by
  let := formalGradedSectionAlgebra f U
  let : Semiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.instSemiring (R := A) (A := Γ(X, U)) (B := I.associatedGraded)
  let : NonAssocSemiring (Γ(X, U) ⊗[A] I.associatedGraded) :=
    (inferInstance : Semiring (Γ(X, U) ⊗[A] I.associatedGraded)).toNonAssocSemiring
  let := formalGradedAffineModule f I F U
  let := formalGradedAffineModule_scalarTower_left f I F U
  change (1 : Γ(X, U) ⊗[A] I.associatedGraded) •
    DirectSum.of (fun n => Γ(F.gradedPiece n, U)) 0 m = _
  exact one_smul _ _

end AlgebraicGeometry.Scheme.Cohomology
