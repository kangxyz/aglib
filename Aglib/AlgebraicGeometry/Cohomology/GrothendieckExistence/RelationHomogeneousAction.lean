/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationScalarLifts

/-! # Native associated-graded coefficients act on the original relation kernels -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  {P F : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : P ⟶ F)

/-- The actual kernel of the graded coefficient map inherits native
associated-graded multiplication from its original naturality square. -/
def relationGradedHomogeneousAction (r n : ℕ) (a : I.associatedGradedGrading r) :
    relationGradedPiece φ n ⟶ relationGradedPiece φ (r + n) :=
  (relationGradedPieceIso φ n).hom ≫
    kernel.map (P.gradedPieceMap φ n) (P.gradedPieceMap φ (r + n))
      (formalGradedHomogeneousAction f I P r n a)
      (formalGradedHomogeneousAction f I F r n a)
      (formalGradedHomogeneousAction_naturality f I φ r n a) ≫
    (relationGradedPieceIso φ (r + n)).inv

@[reassoc (attr := simp)]
theorem relationGradedHomogeneousAction_ι (r n : ℕ)
    (a : I.associatedGradedGrading r) :
    relationGradedHomogeneousAction f I φ r n a ≫ relationGradedι f I φ (r + n) =
      relationGradedι f I φ n ≫ formalGradedHomogeneousAction f I P r n a := by
  simp [relationGradedHomogeneousAction, relationGradedι, Category.assoc]

@[simp]
theorem relationGradedHomogeneousAction_componentMap (r n : ℕ) (a : ↥(I ^ r)) :
    relationGradedHomogeneousAction f I φ r n (I.associatedGradedComponentMap r a) =
      relationGradedScalarMap f I φ r n a := by
  simp only [relationGradedHomogeneousAction, formalGradedHomogeneousAction_componentMap,
    relationGradedScalarMap]

/-- Every native homogeneous action has an original ideal-power representative. -/
theorem exists_relationGradedHomogeneousAction_representative (r n : ℕ)
    (a : I.associatedGradedGrading r) :
    ∃ b : ↥(I ^ r), relationGradedHomogeneousAction f I φ r n a =
      relationGradedScalarMap f I φ r n b := by
  obtain ⟨b, rfl⟩ := I.associatedGradedComponentMap_surjective r a
  exact ⟨b, relationGradedHomogeneousAction_componentMap f I φ r n b⟩

end AlgebraicGeometry.Scheme.Cohomology
