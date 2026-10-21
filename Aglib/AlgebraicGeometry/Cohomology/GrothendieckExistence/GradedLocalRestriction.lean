/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedLocalQuotient
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedChartRestriction
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedTensorRestriction
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.SectionQuotientComparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.RestrictionSections

/-! # Canonical local restriction isomorphisms for formal graded coefficients

The comparison is built from the actual affine section localization maps and
full tensor scalar-extension equivalence. Its section equation is retained,
so subsequent gluing uses original restrictions rather than unrelated isos.
-/

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
  (U V : X.affineOpens) (h : V.val ≤ U.val)

/-- Scalar extension of the literal local coefficient module is the literal
local coefficient on the smaller affine chart. -/
def formalGradedLocalModuleRestrictionIso :
    letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
    letI (W : X.Opens) : Module (Γ(X, W) ⊗[A] I.associatedGraded)
        (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule f I F W
    letI : Algebra Γ(X, U) Γ(X, V) :=
      (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    letI : IsScalarTower A Γ(X, U) Γ(X, V) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        ((formalGradedCoordinateRestriction f h).commutes a).symm
    letI : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
        (Γ(X, V) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
    (ModuleCat.extendScalars (Algebra.TensorProduct.map
      (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom).obj
        (formalGradedLocalModule f I F U) ≅ formalGradedLocalModule f I F V := by
  letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  letI (W : X.Opens) : Module (Γ(X, W) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule f I F W
  letI : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  letI : IsScalarTower A Γ(X, U) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun a =>
        ((formalGradedCoordinateRestriction f h).commutes a).symm
  letI : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
      (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
  exact ModuleCat.extendScalarsAlgebraIso (Γ(X, U) ⊗[A] I.associatedGraded)
      (Γ(X, V) ⊗[A] I.associatedGraded) (formalGradedLocalModule f I F U) ≪≫
    (formalGradedTensorRestrictionEquiv f I F U V (homOfLE h)).toModuleIso

/-- Original affine sections of the restricted local tilde coefficient are
identified with the actual graded sections on the smaller open. -/
def formalGradedLocalRestrictionSectionsIso :
    letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
    letI (W : X.Opens) : Module (Γ(X, W) ⊗[A] I.associatedGraded)
        (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule f I F W
    letI : Algebra Γ(X, U) Γ(X, V) :=
      (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    letI : IsScalarTower A Γ(X, U) Γ(X, V) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        ((formalGradedCoordinateRestriction f h).commutes a).symm
    letI : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
        (Γ(X, V) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
    moduleSpecΓFunctor.obj ((tilde (formalGradedLocalModule f I F U)).restrict
      (formalGradedChartRestriction f I U V h)) ≅ formalGradedLocalModule f I F V := by
  letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  letI (W : X.Opens) : Module (Γ(X, W) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule f I F W
  letI : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  letI : IsScalarTower A Γ(X, U) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun a =>
        ((formalGradedCoordinateRestriction f h).commutes a).symm
  letI : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
      (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
      (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom)) :=
    inferInstanceAs (IsOpenImmersion (formalGradedChartRestriction f I U V h))
  exact (affineRestrictGlobalSectionsIso
    (CommRingCat.ofHom (Algebra.TensorProduct.map
      (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom)
    (tilde (formalGradedLocalModule f I F U))).symm ≪≫
  (ModuleCat.extendScalars (Algebra.TensorProduct.map
    (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom).mapIso
      ((tilde.toTildeΓNatIso (R := CommRingCat.of (Γ(X, U) ⊗[A] I.associatedGraded))).app
        (formalGradedLocalModule f I F U)).symm ≪≫
  formalGradedLocalModuleRestrictionIso f I F U V h

/-- The genuine sheaf restriction isomorphism on the literal tensor charts. -/
def formalGradedLocalRestrictionIso :
    letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
    letI (W : X.Opens) : Module (Γ(X, W) ⊗[A] I.associatedGraded)
        (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule f I F W
    letI : Algebra Γ(X, U) Γ(X, V) :=
      (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    letI : IsScalarTower A Γ(X, U) Γ(X, V) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        ((formalGradedCoordinateRestriction f h).commutes a).symm
    letI : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
        (Γ(X, V) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
    (tilde (formalGradedLocalModule f I F U)).restrict
      (formalGradedChartRestriction f I U V h) ≅ tilde (formalGradedLocalModule f I F V) := by
  letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  letI (W : X.Opens) : Module (Γ(X, W) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule f I F W
  letI : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  letI : IsScalarTower A Γ(X, U) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun a =>
        ((formalGradedCoordinateRestriction f h).commutes a).symm
  letI : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
      (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
  exact affineSheafIsoOfSectionIso _ _ (formalGradedLocalRestrictionSectionsIso f I F U V h)

/-- The local sheaf comparison retains the specified original section comparison. -/
@[reassoc]
theorem formalGradedLocalRestrictionIso_sections :
    letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
    letI (W : X.Opens) : Module (Γ(X, W) ⊗[A] I.associatedGraded)
        (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule f I F W
    letI : Algebra Γ(X, U) Γ(X, V) :=
      (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    letI : IsScalarTower A Γ(X, U) Γ(X, V) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        ((formalGradedCoordinateRestriction f h).commutes a).symm
    letI : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
        (Γ(X, V) ⊗[A] I.associatedGraded) :=
      Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
    moduleSpecΓFunctor.map (formalGradedLocalRestrictionIso f I F U V h).hom ≫
      ((tilde.toTildeΓNatIso (R := CommRingCat.of (Γ(X, V) ⊗[A] I.associatedGraded))).app
        (formalGradedLocalModule f I F V)).inv =
        (formalGradedLocalRestrictionSectionsIso f I F U V h).hom := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  let (W : X.Opens) : Module (Γ(X, W) ⊗[A] I.associatedGraded)
      (⨁ n, Γ(F.gradedPiece n, W)) := formalGradedAffineModule f I F W
  let : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE h).op).hom.toAlgebra
  let : IsScalarTower A Γ(X, U) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun a =>
        ((formalGradedCoordinateRestriction f h).commutes a).symm
  let : Algebra (Γ(X, U) ⊗[A] I.associatedGraded)
      (Γ(X, V) ⊗[A] I.associatedGraded) :=
    Algebra.TensorProduct.coordinateAlgebra A Γ(X, U) Γ(X, V) I.associatedGraded
  exact affineSheafIsoOfSectionIso_sections _ _ _

end AlgebraicGeometry.Scheme.Cohomology
