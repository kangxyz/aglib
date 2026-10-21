/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAffineMap
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAffineFinite
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedNaturality

/-! # Naturality of the original degree-zero graded presentations -/

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

variable {F G : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : F ⟶ G)

/-- The original formal morphism induces a map of the canonical local presentations. -/
theorem formalGradedAffineMap_presentation_tmul :
    letI := formalGradedSectionAlgebra f U
    letI := formalGradedAffineModule f I F U
    letI := formalGradedAffineModule f I G U
    ∀ (c : Γ(X, U) ⊗[A] I.associatedGraded) (y : Γ(F.gradedPiece 0, U)),
    formalGradedAffineMap f I U φ
      (formalGradedAffinePresentation f I F U (c ⊗ₜ[Γ(X, U)] y)) =
      formalGradedAffinePresentation f I G U
        (c ⊗ₜ[Γ(X, U)] ((F.gradedPieceMap φ 0).app U y)) := by
  let := formalGradedSectionAlgebra f U
  let := formalGradedAffineModule f I F U
  let := formalGradedAffineModule f I G U
  intro c y
  change formalGradedAffineMap f I U φ (c • DirectSum.of _ 0 y) = _
  rw [_root_.map_smul, formalGradedAffineMap_of]
  rfl

end AlgebraicGeometry.Scheme.Cohomology
