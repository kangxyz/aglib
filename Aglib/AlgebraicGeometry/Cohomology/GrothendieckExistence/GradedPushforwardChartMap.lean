/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedLocalPushforwardMap
public import Aglib.CategoryTheory.Functor.MapComparisonSquare

/-! # Original chart pushforward squares of realized morphisms -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Coherent
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Cohomology
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  {F G : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : F ⟶ G)
  (P Q : (formalGradedSpace f I).Modules) (g : P ⟶ Q)

/-- Original cartesian base change and the literal local map give the exact
coefficient-map square on every original affine chart. -/
theorem formalGradedPushforwardChartIso_naturality (U : X.affineOpens) :
    letI := formalGradedSectionAlgebra f U
    ∀ (eP : P.restrict (formalGradedChart f I U) ≅
      tilde (R := CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded))
        (formalGradedLocalModule f I F U))
    (eQ : Q.restrict (formalGradedChart f I U) ≅
      tilde (R := CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded))
        (formalGradedLocalModule f I G U))
    (_hg : (Scheme.Modules.restrictFunctor (formalGradedChart f I U)).map g ≫ eQ.hom =
      eP.hom ≫ formalGradedLocalMap f I φ U),
    let pU := Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded)))
    let H := (AffineBaseChange.tensorChartMap_isPullback (A := A) (B := Γ(X, U))
      (C := I.associatedGraded) f U.property.fromSpec (formalGradedChart_over f U)).flip
    Functor.mapComparisonSquare
      (Scheme.Modules.pushforward (formalGradedProjection f I) ⋙
        Scheme.Modules.restrictFunctor U.property.fromSpec)
      (Scheme.Modules.pushforward pU)
      (cartesianOpenBaseChange (formalGradedChart f I U) pU
        (formalGradedProjection f I) U.property.fromSpec H)
      g eP eQ (formalGradedLocalPushforwardIso f I F U)
      (formalGradedLocalPushforwardIso f I G U)
      ((Scheme.Modules.restrictFunctor U.property.fromSpec).map
        (CategoryTheory.Limits.Sigma.map (fun n => F.gradedPieceMap φ n))) := by
  let := formalGradedSectionAlgebra f U
  intro eP eQ hg
  let pU := Spec.map (CommRingCat.ofHom
    (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded)))
  let H := (AffineBaseChange.tensorChartMap_isPullback (A := A) (B := Γ(X, U))
    (C := I.associatedGraded) f U.property.fromSpec (formalGradedChart_over f U)).flip
  exact Functor.mapComparisonSquare_of_local_squares
    (Scheme.Modules.pushforward (formalGradedProjection f I) ⋙
      Scheme.Modules.restrictFunctor U.property.fromSpec)
    (Scheme.Modules.pushforward pU)
    (cartesianOpenBaseChange (formalGradedChart f I U) pU
      (formalGradedProjection f I) U.property.fromSpec H)
    g eP eQ (formalGradedLocalPushforwardIso f I F U)
    (formalGradedLocalPushforwardIso f I G U)
    ((Scheme.Modules.restrictFunctor U.property.fromSpec).map
      (CategoryTheory.Limits.Sigma.map (fun n => F.gradedPieceMap φ n)))
    (formalGradedLocalMap f I φ U) hg
    (formalGradedLocalPushforwardIso_naturality f I φ U)

end AlgebraicGeometry.Scheme.Cohomology
