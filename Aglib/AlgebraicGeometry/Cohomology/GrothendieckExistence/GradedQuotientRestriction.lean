/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedLocalQuotientCoordinates
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedLocalRestrictionUnit
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedAmbientRestrictionSections
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.SectionQuotientRestrictionProperty
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartPullbackPresentationCompatibility
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartScalarRestriction
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedQuotientRestrictionUnits

/-! # Original quotient compatibility on actual graded affine restrictions -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Coherent
open scoped TensorProduct DirectSum ChangeOfRings
namespace AlgebraicGeometry.Scheme.Cohomology
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))
  (U V : X.affineOpens) (h : V.val ≤ U.val)

local instance :
    letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
      (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom)) := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  exact formalGradedChartRestriction_isOpenImmersion f I U V h

/-- The original local section presentations commute with scalar extension and
actual geometric restriction. It suffices to test double unit tensors of the
original degree-zero sections. -/
theorem formalGradedLocalSectionQuotient_restriction :
    letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
    let φ := CommRingCat.ofHom (Algebra.TensorProduct.map
      (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom
    ModuleCat.algebraTensorPresentationCompatible φ.hom
      (formalGradedAmbientSectionsIso f I F U)
      (formalGradedLocalSectionQuotient f I F U)
      (formalGradedLocalSectionQuotient f I F V)
      (formalGradedLocalModuleRestrictionIso f I F U V h).hom
      (affineChartScalarRestriction φ (formalGradedChart f I U) (formalGradedChart f I V)
        (formalGradedChartRestriction_chart f I U V h) (formalGradedAmbient f I F)) := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  let φ := CommRingCat.ofHom (Algebra.TensorProduct.map
    (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom
  exact chartPullbackPresentationCompatible_of_unit_equations
    (formalGradedProjection f I) U.property.fromSpec
    (formalGradedChart f I U) (formalGradedChart f I V) φ
    (formalGradedChartRestriction_chart f I U V h)
    (formalGradedChart_projection f I U) (F.gradedPiece 0)
    (affineChartΓIso U (F.gradedPiece 0))
    (formalGradedLocalSectionQuotient f I F U)
    (formalGradedLocalSectionQuotient f I F V)
    (formalGradedLocalModuleRestrictionIso f I F U V h).hom
    (fun m => DirectSum.of (fun n => Γ(F.gradedPiece n, U)) 0 m)
    (fun m => DirectSum.of (fun n => Γ(F.gradedPiece n, V)) 0
      ((F.gradedPiece 0).val.map (homOfLE h).op m))
    (fun m => formalGradedLocalSectionQuotient_unit_property f I F U m)
    (fun m => formalGradedLocalModuleRestrictionIso_one_tmul_of f I F U V h 0 m)
    (fun m => formalGradedLocalSectionQuotient_restricted_unit f I F U V h m)

/-- The actual canonical quotient maps agree under the genuine local restriction isos. -/
theorem formalGradedLocalQuotient_restriction :
    letI (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
    let φ := CommRingCat.ofHom (Algebra.TensorProduct.map
      (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom
    affineChartQuotientRestrictionEquation φ
      (formalGradedChart f I U) (formalGradedChart f I V)
      (formalGradedChartRestriction_chart f I U V h) (formalGradedAmbient f I F)
      (formalGradedLocalModule f I F U) (formalGradedLocalModule f I F V)
      (formalGradedLocalSectionQuotient f I F U)
      (formalGradedLocalSectionQuotient f I F V)
      (formalGradedLocalModuleRestrictionIso f I F U V h) := by
  let (W : X.Opens) : Algebra A Γ(X, W) := formalGradedSectionAlgebra f W
  let φ := CommRingCat.ofHom (Algebra.TensorProduct.map
    (formalGradedCoordinateRestriction f h) (AlgHom.id A I.associatedGraded)).toRingHom
  exact affineChartQuotientRestrictionEquation_of_presentation φ
    (formalGradedChart f I U) (formalGradedChart f I V)
    (formalGradedChartRestriction_chart f I U V h) (formalGradedAmbient f I F)
    (formalGradedLocalModule f I F U) (formalGradedLocalModule f I F V)
    (formalGradedLocalSectionQuotient f I F U)
    (formalGradedLocalSectionQuotient f I F V)
    (formalGradedLocalModuleRestrictionIso f I F U V h)
    (ModuleCat.of Γ(X, U) Γ(F.gradedPiece 0, U))
    (formalGradedAmbientSectionsIso f I F U)
    (formalGradedLocalSectionQuotient_restriction f I F U V h)

end AlgebraicGeometry.Scheme.Cohomology
