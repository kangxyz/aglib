/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedStageComparison
public import Aglib.RingTheory.AssociatedGraded.Components

/-!
# Actual homogeneous associated-graded scalars acting on a formal coefficient

The additive homogeneous action descends the finite-stage scalar maps through
the original surjection from I^r to the native degree-r associated-graded
component. The next-power vanishing proves representative independence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

/-- The original homogeneous scalar map is additive in its scalar representative. -/
def formalGradedScalarAddHom (r n : ℕ) :
    ↥(I ^ r) →+ (F.gradedPiece n ⟶ F.gradedPiece (r + n)) where
  toFun := formalGradedScalarMap f I F r n
  map_zero' := formalGradedScalarMap_eq_zero f I F r n 0 (by simp)
  map_add' a b := by
    simp only [formalGradedScalarMap, idealPowerQuotientLayerMul, Submodule.coe_add]
    rw [← Preadditive.comp_add, ← Preadditive.add_comp]
    apply congrArg (fun g => _ ≫ g ≫ _)
    exact idealQuotientLayerMul_add X (idealThickeningBaseScalar f)
      (F.obj.obj (op (r + n + 1))) _ _ (a : A) b _ _ _ _

/-- The original degree-r associated-graded component acts on degree n.
This is independent of all scalar representatives by the proved kernel equality. -/
def formalGradedHomogeneousAction (r n : ℕ) :
    I.associatedGradedGrading r →+ (F.gradedPiece n ⟶ F.gradedPiece (r + n)) :=
  (I.associatedGradedComponentMap r).toAddMonoidHom.liftOfSurjective
    (I.associatedGradedComponentMap_surjective r)
    ⟨formalGradedScalarAddHom f I F r n, by
      intro a ha
      change formalGradedScalarMap f I F r n a = 0
      apply formalGradedScalarMap_eq_zero
      exact (I.associatedGradedComponentMap_eq_zero_iff r a).mp ha⟩

/-- On the original homogeneous coefficient, the action is the original
finite-stage scalar map, not a separately chosen action. -/
@[simp]
theorem formalGradedHomogeneousAction_componentMap (r n : ℕ) (a : ↥(I ^ r)) :
    formalGradedHomogeneousAction f I F r n (I.associatedGradedComponentMap r a) =
      formalGradedScalarMap f I F r n a := by
  exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a

end AlgebraicGeometry.Scheme.Cohomology
