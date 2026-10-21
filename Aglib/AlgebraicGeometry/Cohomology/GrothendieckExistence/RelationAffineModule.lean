/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationGradedSections
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAffineMap
public import Aglib.RingTheory.AssociatedGraded.TensorRing
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.RingTheory.Noetherian.Basic

/-! # The actual finite tensor module on original relation graded sections -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite DirectSum
open scoped TensorProduct
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (U : X.Opens)
  {P F : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : P ⟶ F)

/-- The original tensor-coordinate ring acts on the coefficient graded section total. -/
local instance (G : AdicSystem X (idealThickeningIdealSheaf f I)) :
    letI := formalGradedSectionAlgebra f U
    Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(G.gradedPiece n, U)) := by
  letI := formalGradedSectionAlgebra f U
  exact formalGradedAffineModule f I G U

/-- The original graded relation total is the additive group underlying the
kernel of the actual same-chart tensor-linear coefficient map. -/
def relationGradedAffineKernelAddEquiv :
    letI := formalGradedSectionAlgebra f U
    (⨁ n, Γ(relationGradedPiece φ n, U)) ≃+
      (formalGradedAffineMap f I U φ).ker := by
  letI := formalGradedSectionAlgebra f U
  exact (relationGradedTotalKernelEquiv φ U).toAddEquiv

/-- Transport the actual tensor-kernel action to the original relation total. -/
@[instance_reducible]
def relationGradedAffineModule :
    letI := formalGradedSectionAlgebra f U
    Module (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(relationGradedPiece φ n, U)) := by
  letI := formalGradedSectionAlgebra f U
  exact (relationGradedAffineKernelAddEquiv f I U φ).module (Γ(X, U) ⊗[A] I.associatedGraded)

/-- The original relation total is finite because it is the actual kernel
inside a finite module over a Noetherian tensor coefficient ring. No degree-zero
generation claim about this kernel is used. -/
theorem relationGradedAffineModule_finite :
    letI := formalGradedSectionAlgebra f U
    ∀ [IsNoetherianRing (Γ(X, U) ⊗[A] I.associatedGraded)]
      [Module.Finite (Γ(X, U) ⊗[A] I.associatedGraded) (⨁ n, Γ(P.gradedPiece n, U))],
    letI := relationGradedAffineModule f I U φ
    Module.Finite (Γ(X, U) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(relationGradedPiece φ n, U)) := by
  let := formalGradedSectionAlgebra f U
  intro hnoeth hfinite
  let := relationGradedAffineModule f I U φ
  exact Module.Finite.equiv
    ((relationGradedAffineKernelAddEquiv f I U φ).linearEquiv
      (Γ(X, U) ⊗[A] I.associatedGraded)).symm

end AlgebraicGeometry.Scheme.Cohomology
