/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedPushforwardRestriction
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedLocalRestrictionUnit
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.PushforwardChartRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.CoproductSectionRestriction

/-! # Original section coordinates for graded pushforward comparisons -/

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

/-- The original tilde, scalar restriction, and coproduct section coordinates. -/
def formalGradedPushforwardSectionCoordinates (U : X.affineOpens) :
  letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  letI (W : X.Opens) : Module (Γ(X, W) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule f I F W
  letI (W : X.Opens) : IsScalarTower Γ(X, W) (Γ(X, W) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule_scalarTower_left f I F W
  letI : F.gradedUnderlying.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_coproduct F.gradedPiece
  moduleSpecΓFunctor.obj (tilde (R := CommRingCat.of
    (Γ(X, U) ⊗[A] I.associatedGraded)) (formalGradedLocalModule f I F U)) →+
    Γ(F.gradedUnderlying, U) := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  let (W : X.Opens) : Module (Γ(X, W) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule f I F W
  let (W : X.Opens) : IsScalarTower Γ(X, W) (Γ(X, W) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule_scalarTower_left f I F W
  let : F.gradedUnderlying.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_coproduct F.gradedPiece
  exact (QuasiCoherent.affineOpenSectionsCoproductIso F.gradedPiece U).inv.hom.toAddMonoidHom.comp
    ((formalGradedLocalForgetIso f I F U).hom.hom.toAddMonoidHom.comp
      (((tilde.toTildeΓNatIso
        (R := CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded))).app
          (formalGradedLocalModule f I F U)).inv.hom.toAddMonoidHom))

/-- These coordinates evaluate the actual local pushforward comparison. -/
theorem formalGradedLocalPushforward_coordinates (U : X.affineOpens) :
  letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  letI (W : X.Opens) : Module (Γ(X, W) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule f I F W
  letI (W : X.Opens) : IsScalarTower Γ(X, W) (Γ(X, W) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule_scalarTower_left f I F W
  letI : F.gradedUnderlying.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_coproduct F.gradedPiece
  PushforwardChartCoordinates U (CommRingCat.ofHom
    (algebraMap Γ(X, U) (Γ(X, U) ⊗[A] I.associatedGraded))) F.gradedUnderlying
    (tilde (formalGradedLocalModule f I F U))
    (formalGradedLocalPushforwardIso f I F U).hom
    (formalGradedPushforwardSectionCoordinates f I F U) := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  let (W : X.Opens) : Module (Γ(X, W) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule f I F W
  let (W : X.Opens) : IsScalarTower Γ(X, W) (Γ(X, W) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule_scalarTower_left f I F W
  let : F.gradedUnderlying.IsQuasicoherent :=
    QuasiCoherent.quasicoherent_coproduct F.gradedPiece
  intro m
  have he := congrArg (fun q => q ≫
    (QuasiCoherent.affineOpenSectionsCoproductIso F.gradedPiece U).inv)
      (formalGradedLocalPushforwardIso_sections f I F U)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at he
  have hp := congrArg (fun q => q m) he
  change @Eq ((∐ F.gradedPiece).val.obj (Opposite.op U.val)) _ _
  simp only [ConcreteCategory.comp_apply] at hp
  exact hp

/-- Original local coefficient restrictions preserve the original section coordinates. -/
theorem formalGradedPushforward_coordinates_restriction_of
    (U V : X.affineOpens) (h : V.val ≤ U.val)
    (k : ℕ) (x : Γ(F.gradedPiece k, U)) :
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
  let ψ := CommRingCat.ofHom (Algebra.TensorProduct.map
    (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom
  letI : IsOpenImmersion (Spec.map ψ) :=
    inferInstanceAs (IsOpenImmersion (formalGradedChartRestriction f I U V h))
  let NU := formalGradedLocalModule f I F U
  let tU := ((tilde.toTildeΓNatIso
    (R := CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded))).app NU)
  (formalGradedPushforwardSectionCoordinates f I F V)
    (moduleSpecΓFunctor.map (formalGradedLocalRestrictionIso f I F U V h).hom
      (affineRestrictionUnitSection ψ (tilde NU)
        (tU.hom (DirectSum.of (fun n => Γ(F.gradedPiece n, U)) k x)))) =
    F.gradedUnderlying.presheaf.map (homOfLE h).op
      ((formalGradedPushforwardSectionCoordinates f I F U)
        (tU.hom (DirectSum.of (fun n => Γ(F.gradedPiece n, U)) k x))) := by
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
  let ψ := CommRingCat.ofHom (Algebra.TensorProduct.map
    (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom
  let : IsOpenImmersion (Spec.map ψ) :=
    inferInstanceAs (IsOpenImmersion (formalGradedChartRestriction f I U V h))
  let NU := formalGradedLocalModule f I F U
  let NV := formalGradedLocalModule f I F V
  let tU := ((tilde.toTildeΓNatIso
    (R := CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded))).app NU)
  change (QuasiCoherent.affineOpenSectionsCoproductIso F.gradedPiece V).inv
    (((tilde.toTildeΓNatIso
      (R := CommRingCat.of (Γ(X, V) ⊗[A] I.associatedGraded))).app NV).inv
        (moduleSpecΓFunctor.map (formalGradedLocalRestrictionIso f I F U V h).hom
          (affineRestrictionUnitSection ψ (tilde NU)
            (tU.hom (DirectSum.of (fun n => Γ(F.gradedPiece n, U)) k x))))) =
    F.gradedUnderlying.presheaf.map (homOfLE h).op
      ((QuasiCoherent.affineOpenSectionsCoproductIso F.gradedPiece U).inv
        (tU.inv (tU.hom (DirectSum.of (fun n => Γ(F.gradedPiece n, U)) k x))))
  rw [Iso.hom_inv_id_apply,
    QuasiCoherent.affineOpenSectionsCoproductIso_inv_restriction_of]
  congr 1
  exact formalGradedLocalRestrictionIso_unit_of f I F U V h k x

/-- Original local coefficient restrictions preserve the original section coordinates. -/
theorem formalGradedPushforward_coordinates_restriction
    (U V : X.affineOpens) (h : V.val ≤ U.val) :
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
  let ψ := CommRingCat.ofHom (Algebra.TensorProduct.map
    (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom
  letI : IsOpenImmersion (Spec.map ψ) :=
    inferInstanceAs (IsOpenImmersion (formalGradedChartRestriction f I U V h))
  PushforwardChartCoordinateCompatibility U V h ψ F.gradedUnderlying
    (tilde (formalGradedLocalModule f I F U)) (tilde (formalGradedLocalModule f I F V))
    (formalGradedLocalRestrictionIso f I F U V h).hom
    (formalGradedPushforwardSectionCoordinates f I F U)
    (formalGradedPushforwardSectionCoordinates f I F V) := by
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
  let ψ := CommRingCat.ofHom (Algebra.TensorProduct.map
    (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom
  let : IsOpenImmersion (Spec.map ψ) :=
    inferInstanceAs (IsOpenImmersion (formalGradedChartRestriction f I U V h))
  let NU := formalGradedLocalModule f I F U
  let NV := formalGradedLocalModule f I F V
  let tU := ((tilde.toTildeΓNatIso
    (R := CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded))).app NU)
  let sU := formalGradedPushforwardSectionCoordinates f I F U
  let sV := formalGradedPushforwardSectionCoordinates f I F V
  let L := sV.comp ((moduleSpecΓFunctor.map
    (formalGradedLocalRestrictionIso f I F U V h).hom).hom.toAddMonoidHom.comp
      (affineRestrictionUnitSectionAddHom ψ (tilde NU)))
  let R := (F.gradedUnderlying.presheaf.map (homOfLE h).op).hom.comp sU
  have hh : L.comp tU.hom.hom.toAddMonoidHom = R.comp tU.hom.hom.toAddMonoidHom := by
    apply DirectSum.addHom_ext
    intro k x
    exact formalGradedPushforward_coordinates_restriction_of f I F U V h k x
  change ∀ x, L x = R x
  intro x
  obtain ⟨z, rfl⟩ := tU.toLinearEquiv.surjective x
  exact DFunLike.congr_fun hh z

end AlgebraicGeometry.Scheme.Cohomology
