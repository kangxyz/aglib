/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedPushforwardCoordinates

/-! # Native local graded pushforward squares on nested affine charts -/

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

/-- The actual local pushforward comparisons commute with nested chart
restriction, through the original cartesian open base-change map. -/
theorem formalGradedLocalPushforwardIso_restriction :
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
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
      (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom)) :=
    inferInstanceAs (IsOpenImmersion (formalGradedChartRestriction f I U V h))
  ∀ (H : IsPullback (formalGradedChartRestriction f I U V h)
      (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, V) (Γ(X, V) ⊗[A] I.associatedGraded))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded))))
      (Spec.map (X.presheaf.map (homOfLE h).op))),
    PushforwardChartRestrictionSquare U V h
      (CommRingCat.ofHom
        (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded)))
      (CommRingCat.ofHom
        (algebraMap Γ(X, V) (Γ(X, V) ⊗[A] I.associatedGraded)))
      (CommRingCat.ofHom (Algebra.TensorProduct.map
        (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom)
      H F.gradedUnderlying (tilde (formalGradedLocalModule f I F U))
      (tilde (formalGradedLocalModule f I F V))
      (formalGradedLocalRestrictionIso f I F U V h).hom
      (formalGradedLocalPushforwardIso f I F U).hom
      (formalGradedLocalPushforwardIso f I F V).hom := by
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
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
      (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom)) :=
    inferInstanceAs (IsOpenImmersion (formalGradedChartRestriction f I U V h))
  intro H
  dsimp only [formalGradedChartRestriction] at H
  let pU := CommRingCat.ofHom (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded))
  let pV := CommRingCat.ofHom (algebraMap Γ(X, V) (Γ(X, V) ⊗[A] I.associatedGraded))
  let φ := X.presheaf.map (homOfLE h).op
  let ψ := CommRingCat.ofHom (Algebra.TensorProduct.map
    (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom
  set_option backward.isDefEq.respectTransparency true in
    have hH : IsPullback (Spec.map ψ) (Spec.map pV) (Spec.map pU) (Spec.map φ) := H
  let : ((Scheme.Modules.pushforward (Spec.map pU)).obj
      (tilde (formalGradedLocalModule f I F U))).IsQuasicoherent :=
    isQuasicoherent_pushforward pU (tilde (formalGradedLocalModule f I F U))
  exact pushforwardChart_restriction_of_coordinates U V h pU pV ψ hH
    F.gradedUnderlying (tilde (formalGradedLocalModule f I F U))
    (tilde (formalGradedLocalModule f I F V))
    (formalGradedLocalRestrictionIso f I F U V h).hom
    (formalGradedLocalPushforwardIso f I F U).hom
    (formalGradedLocalPushforwardIso f I F V).hom
    (formalGradedPushforwardSectionCoordinates f I F U)
    (formalGradedPushforwardSectionCoordinates f I F V)
    (formalGradedLocalPushforward_coordinates f I F U)
    (formalGradedLocalPushforward_coordinates f I F V)
    (formalGradedPushforward_coordinates_restriction f I F U V h)

end AlgebraicGeometry.Scheme.Cohomology
