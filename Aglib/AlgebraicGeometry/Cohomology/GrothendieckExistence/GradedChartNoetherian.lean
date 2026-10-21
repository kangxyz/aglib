/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedGeometry
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Noetherianity of the actual graded tensor-coordinate rings -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType f] (I : Ideal A)
  (U : X.affineOpens)

/-- The actual tensor-coordinate ring is Noetherian, by its open immersion
into the original locally finite-type graded base change. -/
theorem formalGradedChart_noetherian :
    letI := formalGradedSectionAlgebra f U
    IsNoetherianRing (Γ(X, U) ⊗[A] I.associatedGraded) := by
  let := formalGradedSectionAlgebra f U
  let : IsLocallyNoetherian (formalGradedSpace f I) :=
    inferInstanceAs (IsLocallyNoetherian
      (pullback f (Spec.map (CommRingCat.ofHom (R := A) (S := I.associatedGraded)
        (algebraMap A I.associatedGraded)))))
  exact isLocallyNoetherian_Spec.mp
    (isLocallyNoetherian_of_isOpenImmersion (formalGradedChart f I U))

end AlgebraicGeometry.Scheme.Cohomology
