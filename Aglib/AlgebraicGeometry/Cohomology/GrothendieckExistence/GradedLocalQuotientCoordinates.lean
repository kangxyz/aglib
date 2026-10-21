/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedLocalQuotient

/-! # Original degree-zero coordinates of local graded quotients -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Coherent
open scoped TensorProduct DirectSum ChangeOfRings
namespace AlgebraicGeometry.Scheme.Cohomology
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))
  (U : X.affineOpens)

/-- The local section presentation retains the original degree-zero inclusion. -/
theorem formalGradedLocalSectionQuotient_inv_one_tmul (m : Γ(F.gradedPiece 0, U)) :
    letI := formalGradedSectionAlgebra f U
    letI : Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) :=
      formalGradedAffineModule f I F U
    formalGradedLocalSectionQuotient f I F U
      ((formalGradedAmbientSectionsIso f I F U).inv
        ((1 : Γ(X, U) ⊗[A] I.associatedGraded) ⊗ₜ[Γ(X, U)] m)) =
      DirectSum.of (fun n => Γ(F.gradedPiece n, U)) 0 m := by
  let := formalGradedSectionAlgebra f U
  let : Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(F.gradedPiece n, U)) :=
    formalGradedAffineModule f I F U
  dsimp only [formalGradedLocalSectionQuotient, ModuleCat.comp_apply, ModuleCat.ofHom_hom]
  rw [ConcreteCategory.comp_apply]
  erw [Iso.inv_hom_id_apply]
  change (1 : Γ(X, U) ⊗[A] I.associatedGraded) •
    DirectSum.of (fun n => Γ(F.gradedPiece n, U)) 0 m = _
  exact one_smul _ _

end AlgebraicGeometry.Scheme.Cohomology
