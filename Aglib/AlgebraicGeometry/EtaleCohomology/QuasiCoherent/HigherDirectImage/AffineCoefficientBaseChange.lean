/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.CoefficientNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.AffineBaseChange

/-! # Native affine higher-image coefficient comparison

The original affine section/cohomology comparison followed by the original
étale comparison carries the actual derived coefficient map to its original
étale cohomology coefficient map. All coefficients remain arbitrary.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry.Scheme.Cohomology

universe u e e'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] HasExt.standard hasSheafifyLarge
  moduleComparisonEnoughSmall moduleComparisonEnoughRaised
  moduleComparisonAbWRaised moduleComparisonTypeWRaised

/-- Complete original affine base-change square followed by an arbitrary
native coefficient morphism on the cartesian source. -/
theorem moduleCohomologyComparison_affineFlatBaseChange_coefficient_unit
    {R T : CommRingCat.{u}} {X Y : Scheme.{u}}
    (a : Y ⟶ X) (b : Y ⟶ Spec T) (f : X ⟶ Spec R)
    [QuasiCompact f] [QuasiSeparated f] (φ : R ⟶ T) [Flat (Spec.map φ)]
    (h : IsPullback a b f (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] (N : Y.Modules) [N.IsQuasicoherent]
    (v : (Scheme.Modules.pullback a).obj M ⟶ N)
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((Scheme.Modules.pullback a).obj M))
    (K : InjectiveResolution N) (q : ℕ)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{e'} (AbelianSheaf.{u, u + 1} Y)]
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj M)) :
    let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
    @Eq (Sheaf.H.{e'} (additiveCoefficient Y N) q)
      (moduleCohomologyComparison.{u, u + 1, e'} Y N q
        (moduleHigherDirectImageAffineSectionsLinearEquiv b N K q
          ((moduleSpecΓFunctor (R := T)).map
            (((Scheme.Modules.pushforward b).rightDerived q).map v)
            ((moduleSpecΓFunctor (R := T)).map
              ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f (Spec.map φ) h q).app M)
              ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
                (((Scheme.Modules.pushforward f).rightDerived q).obj M)).app ⊤) x)))))
      (Sheaf.H.map (additiveCoefficientMap Y v) q
        (additiveCoefficientCohomologyPullback.{u, e, e'} a M q
          (moduleCohomologyComparison.{u, u + 1, e} X M q
            (moduleHigherDirectImageAffineSectionsLinearEquiv f M I q x)))) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  let z := (moduleSpecΓFunctor (R := T)).map
    ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f (Spec.map φ) h q).app M)
    ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
      (((Scheme.Modules.pushforward f).rightDerived q).obj M)).app ⊤) x)
  have hc := moduleCohomologyComparison_affineSections_naturality.{u, e'} b v J K q z
  have hb := moduleCohomologyComparison_affineFlatBaseChange_unit.{u, e, e'}
    a b f φ h M I J q x
  exact hc.trans (congrArg (Sheaf.H.map (additiveCoefficientMap Y v) q) hb)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
