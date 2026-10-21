/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedChartRestriction

/-! # The actual cartesian square of nested graded tensor charts -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Cohomology
variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (U V : X.affineOpens) (h : V.val ≤ U.val)

/-- Both nested tensor charts are base changes of the original affine opens,
so their original coordinate restriction square is cartesian. -/
theorem formalGradedChartRestriction_isPullback :
    letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
    IsPullback (formalGradedChartRestriction f I U V h)
      (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, V) (Γ(X, V) ⊗[A] I.associatedGraded))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded))))
      (Spec.map (CommRingCat.ofHom (formalGradedCoordinateRestriction f h).toRingHom)) := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  have hw : formalGradedChartRestriction f I U V h ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, V) (Γ(X, V) ⊗[A] I.associatedGraded))) ≫
      Spec.map (CommRingCat.ofHom (formalGradedCoordinateRestriction f h).toRingHom) := by
    dsimp only [formalGradedChartRestriction]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have HU := (AffineBaseChange.tensorChartMap_isPullback (A := A) (B := Γ(X, U))
    (C := I.associatedGraded) f U.property.fromSpec (formalGradedChart_over f U)).flip
  have HV := (AffineBaseChange.tensorChartMap_isPullback (A := A) (B := Γ(X, V))
    (C := I.associatedGraded) f V.property.fromSpec (formalGradedChart_over f V)).flip
  apply (HU.paste_horiz_iff hw).mp
  rw [show AffineBaseChange.tensorChartMap (A := A) (B := Γ(X, U))
      (C := I.associatedGraded) f U.property.fromSpec (formalGradedChart_over f U) =
        formalGradedChart f I U from rfl,
    formalGradedChartRestriction_chart]
  have hb : Spec.map (CommRingCat.ofHom (formalGradedCoordinateRestriction f h).toRingHom) ≫
      U.property.fromSpec = V.property.fromSpec :=
    U.property.map_fromSpec V.property (homOfLE h).op
  rw [hb]
  exact HV

end AlgebraicGeometry.Scheme.Cohomology
