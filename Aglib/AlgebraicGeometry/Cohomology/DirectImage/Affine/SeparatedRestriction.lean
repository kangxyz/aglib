/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.SeparatedCohomology
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.CounitRestriction

/-! # Original affine open restriction: actual separated adapter -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Cohomology
universe u

-- The native unit and its scalar-forgetting component have deeply nested functor types.
set_option maxRecDepth 2000 in
/-- On an actual affine cartesian open square, the original higher-image comparison
becomes the original geometric cohomology map under the original affine section
comparisons. Target qcqs follows from the supplied cartesian square. -/
theorem moduleHigherDirectImageAffineSectionsLinearEquiv_openRestriction_of_isSeparated
    {R S : CommRingCat.{u}} {X Y : Scheme.{u}}
    (a : Y ⟶ X) (b : Y ⟶ Spec S) (f : X ⟶ Spec R)
    [QuasiCompact f] [IsSeparated f] (φ : R ⟶ S)
    [IsOpenImmersion a] [IsOpenImmersion (Spec.map φ)]
    (h : IsPullback a b f (Spec.map φ)) (M : X.Modules) [M.IsQuasicoherent]
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((Scheme.Modules.restrictFunctor a).obj M)) (n : ℕ)
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    letI : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
    letI : IsSeparated b := MorphismProperty.of_isPullback h inferInstance
    moduleHigherDirectImageAffineSectionsLinearEquiv_of_isSeparated b
        ((Scheme.Modules.restrictFunctor a).obj M) J n
        ((moduleSpecΓFunctor (R := S)).map
          ((Scheme.Modules.higherDirectImageOpenRestrictionIso a b f (Spec.map φ) h n).hom.app M)
          ((((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.app
            (((Scheme.Modules.pushforward f).rightDerived n).obj M)).app ⊤) x)) =
      moduleCohomologyMapAlong a ((Scheme.Modules.restrictAdjunction a).unit.app M) n
        (moduleHigherDirectImageAffineSectionsLinearEquiv_of_isSeparated f M I n x) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : IsSeparated b := MorphismProperty.of_isPullback h inferInstance
  let := moduleResolutionPushforwardTildeCounit_quasiIso_of_isSeparated f M I
  let := moduleResolutionPushforwardTildeCounit_quasiIso_of_isSeparated b
    ((Scheme.Modules.restrictFunctor a).obj M) J
  exact moduleHigherDirectImageAffineSectionsLinearEquiv_openRestriction_of_counit_quasiIso
    a b f φ h M I J n x

end AlgebraicGeometry.Scheme.Cohomology
