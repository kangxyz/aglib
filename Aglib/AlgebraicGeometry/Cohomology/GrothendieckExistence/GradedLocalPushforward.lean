/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedLocalQuotient
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAffineScalars
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.CoproductSectionIso
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian

/-! # Original local pushforward comparisons for formal graded realization -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open scoped TensorProduct DirectSum

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I)) (U : X.affineOpens)

/-- Forgetting only the tensor-ring action gives exactly the actual direct sum
of original section modules, with its original coordinate-ring action. -/
def formalGradedLocalForgetIso :
    letI := formalGradedSectionAlgebra f U
    letI := formalGradedAffineModule f I F U
    letI := formalGradedAffineModule_scalarTower_left f I F U
    letI : F.gradedUnderlying.IsQuasicoherent :=
      QuasiCoherent.quasicoherent_coproduct F.gradedPiece
    (ModuleCat.restrictScalars (algebraMap Γ(X, U)
      (Γ(X, U) ⊗[A] I.associatedGraded))).obj (formalGradedLocalModule f I F U) ≅
        ModuleCat.of Γ(X, U) (⨁ n, Γ(F.gradedPiece n, U)) := by
  letI := formalGradedSectionAlgebra f U
  letI := formalGradedAffineModule f I F U
  letI := formalGradedAffineModule_scalarTower_left f I F U
  letI : F.gradedUnderlying.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_coproduct F.gradedPiece
  letI : Module Γ(X, U) (formalGradedLocalModule f I F U) :=
    inferInstanceAs (Module Γ(X, U) (⨁ n, Γ(F.gradedPiece n, U)))
  letI : IsScalarTower Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded)
      (formalGradedLocalModule f I F U) :=
    formalGradedAffineModule_scalarTower_left f I F U
  exact ModuleCat.restrictScalarsAlgebraIso Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded)
    (formalGradedLocalModule f I F U)

/-- The actual coproduct coefficient on an affine chart is the tilde of the
literal direct sum, through its original coproduct inclusions and affine counit. -/
def formalGradedCoproductChartIso :
    letI := formalGradedSectionAlgebra f U
    letI := formalGradedAffineModule f I F U
    letI := formalGradedAffineModule_scalarTower_left f I F U
    letI : F.gradedUnderlying.IsQuasicoherent :=
      QuasiCoherent.quasicoherent_coproduct F.gradedPiece
    F.gradedUnderlying.restrict U.property.fromSpec ≅
      tilde (ModuleCat.of Γ(X, U) (⨁ n, Γ(F.gradedPiece n, U))) := by
  letI := formalGradedSectionAlgebra f U
  letI := formalGradedAffineModule f I F U
  letI := formalGradedAffineModule_scalarTower_left f I F U
  letI : F.gradedUnderlying.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_coproduct F.gradedPiece
  exact (asIso (F.gradedUnderlying.restrict U.property.fromSpec).fromTildeΓ).symm ≪≫
    (tilde.functor Γ(X, U)).mapIso
      (affineChartΓIso U F.gradedUnderlying ≪≫
        QuasiCoherent.affineOpenSectionsCoproductIso F.gradedPiece U)

/-- Direct image of the actual local graded tilde coefficient recovers the
original coproduct coefficient, not an abstract graded replacement. -/
def formalGradedLocalPushforwardIso :
    letI := formalGradedSectionAlgebra f U
    letI := formalGradedAffineModule f I F U
    letI := formalGradedAffineModule_scalarTower_left f I F U
    letI : F.gradedUnderlying.IsQuasicoherent :=
      QuasiCoherent.quasicoherent_coproduct F.gradedPiece
    (pushforward (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded))))).obj
        (tilde (formalGradedLocalModule f I F U)) ≅
      F.gradedUnderlying.restrict U.property.fromSpec := by
  letI := formalGradedSectionAlgebra f U
  letI := formalGradedAffineModule f I F U
  letI := formalGradedAffineModule_scalarTower_left f I F U
  letI : F.gradedUnderlying.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_coproduct F.gradedPiece
  exact (tildePushforwardIso (CommRingCat.ofHom
    (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded)))).app
      (formalGradedLocalModule f I F U) ≪≫
    (tilde.functor Γ(X, U)).mapIso (formalGradedLocalForgetIso f I F U) ≪≫
      (formalGradedCoproductChartIso f I F U).symm

/-- Any realized local coefficient gives the original pushforward comparison
on that original affine chart, using the actual cartesian open base change. -/
def formalGradedPushforwardChartIso (G : (formalGradedSpace f I).Modules)
    (c : G.restrict (formalGradedChart f I U) ≅ tilde (formalGradedLocalModule f I F U)) :
    letI := formalGradedSectionAlgebra f U
    letI := formalGradedAffineModule f I F U
    letI := formalGradedAffineModule_scalarTower_left f I F U
    letI : F.gradedUnderlying.IsQuasicoherent :=
      QuasiCoherent.quasicoherent_coproduct F.gradedPiece
    ((pushforward (formalGradedProjection f I)).obj G).restrict U.property.fromSpec ≅
      F.gradedUnderlying.restrict U.property.fromSpec := by
  letI := formalGradedSectionAlgebra f U
  letI := formalGradedAffineModule f I F U
  letI := formalGradedAffineModule_scalarTower_left f I F U
  letI : F.gradedUnderlying.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_coproduct F.gradedPiece
  exact (cartesianOpenBaseChange (formalGradedChart f I U)
    (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded))))
    (formalGradedProjection f I) U.property.fromSpec
    (AffineBaseChange.tensorChartMap_isPullback (A := A) (B := Γ(X, U))
      (C := I.associatedGraded) f U.property.fromSpec
      (formalGradedChart_over f U)).flip).app G ≪≫
    (pushforward (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded))))).mapIso c ≪≫
    formalGradedLocalPushforwardIso f I F U

end AlgebraicGeometry.Scheme.Cohomology
