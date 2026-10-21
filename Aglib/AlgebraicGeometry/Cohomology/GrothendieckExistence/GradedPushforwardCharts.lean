/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedPushforwardNaturality
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedChartRestrictionSquare
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.RefinementComparisons

/-! # Native realized graded pushforward comparisons on nested affine charts -/

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
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

variable (U V : X.affineOpens) (h : V.val ≤ U.val)

/-- The original pushforward comparisons of a realized coefficient commute
with chart refinement whenever its actual local coefficient isomorphisms do. -/
theorem formalGradedPushforwardChartIso_restriction :
  letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  letI (W : X.Opens) : Module (Γ(X, W) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule f I F W
  letI (W : X.Opens) : IsScalarTower Γ(X, W) (Γ(X, W) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule_scalarTower_left f I F W
  letI : F.gradedUnderlying.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_coproduct F.gradedPiece
  letI : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  letI : IsScalarTower A Γ(X, U) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      ((formalGradedCoordinateRestriction f h).commutes a).symm
  letI : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
      (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
  letI : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE h).op)) := by
    have hc := U.property.map_fromSpec V.property (homOfLE h).op
    have : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE h).op) ≫ U.property.fromSpec) :=
      hc ▸ inferInstance
    exact IsOpenImmersion.of_comp _ U.property.fromSpec
  ∀     (G : (formalGradedSpace f I).Modules)
    (eU : G.restrict (formalGradedChart f I U) ≅ tilde (formalGradedLocalModule f I F U))
    (eV : G.restrict (formalGradedChart f I V) ≅ tilde (formalGradedLocalModule f I F V))
    (_he : (Scheme.Modules.restrictFunctor (formalGradedChartRestriction f I U V h)).map eU.hom ≫
        (formalGradedLocalRestrictionIso f I F U V h).hom =
      ((restrictFunctorComp (formalGradedChartRestriction f I U V h)
        (formalGradedChart f I U)).symm.app G ≪≫
        (restrictFunctorCongr (formalGradedChartRestriction_chart f I U V h)).app G).hom ≫
          eV.hom),
    RestrictionComparisonSquare U.property.fromSpec V.property.fromSpec
      (Spec.map (X.presheaf.map (homOfLE h).op))
      (U.property.map_fromSpec V.property (homOfLE h).op)
      ((Scheme.Modules.pushforward (formalGradedProjection f I)).obj G) F.gradedUnderlying
      (formalGradedPushforwardChartIso f I F U G eU).hom
      (formalGradedPushforwardChartIso f I F V G eV).hom := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  let (W : X.Opens) : Module (Γ(X, W) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule f I F W
  let (W : X.Opens) : IsScalarTower Γ(X, W) (Γ(X, W) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule_scalarTower_left f I F W
  let : F.gradedUnderlying.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_coproduct F.gradedPiece
  let : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  let : IsScalarTower A Γ(X, U) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      ((formalGradedCoordinateRestriction f h).commutes a).symm
  let : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
      (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
  let : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE h).op)) := by
    have hc := U.property.map_fromSpec V.property (homOfLE h).op
    have : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE h).op) ≫ U.property.fromSpec) :=
      hc ▸ inferInstance
    exact IsOpenImmersion.of_comp _ U.property.fromSpec
  intro G eU eV he
  let HU := (AffineBaseChange.tensorChartMap_isPullback (A := A) (B := Γ(X, U))
    (C := I.associatedGraded) f U.property.fromSpec (formalGradedChart_over f U)).flip
  let HV := (AffineBaseChange.tensorChartMap_isPullback (A := A) (B := Γ(X, V))
    (C := I.associatedGraded) f V.property.fromSpec (formalGradedChart_over f V)).flip
  let HW := formalGradedChartRestriction_isPullback f I U V h
  have hlocal := formalGradedLocalPushforwardIso_restriction f I F U V h HW
  unfold PushforwardChartRestrictionSquare at hlocal
  exact cartesianOpenBaseChange_refinement_comparison
    (formalGradedProjection f I) U.property.fromSpec V.property.fromSpec
    (Spec.map (X.presheaf.map (homOfLE h).op))
    (formalGradedChart f I U) (formalGradedChart f I V)
    (formalGradedChartRestriction f I U V h)
    (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded))))
    (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, V) (Γ(X, V) ⊗[A] I.associatedGraded))))
    (U.property.map_fromSpec V.property (homOfLE h).op)
    (formalGradedChartRestriction_chart f I U V h) HU HV HW
    G F.gradedUnderlying (tilde (formalGradedLocalModule f I F U))
    (tilde (formalGradedLocalModule f I F V)) eU eV
    (formalGradedLocalRestrictionIso f I F U V h)
    (formalGradedLocalPushforwardIso f I F U) (formalGradedLocalPushforwardIso f I F V)
    he hlocal

end AlgebraicGeometry.Scheme.Cohomology
