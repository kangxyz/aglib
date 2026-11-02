/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ModuleCohomologyNaturality
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.FlatComparison.Affine

/-! # Original affine higher-image base change in étale cohomology

The original native flat base-change map, evaluated on the original section
unit, becomes actual geometric étale cohomology pullback. Both absolute
comparisons and both Ext ranges remain explicit. This is the geometric
transition equation, before inverse étale coefficient transport or pasting.
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

/-- The original higher-image map on the section unit agrees with actual étale
geometric pullback under the unchanged native affine and absolute comparisons.
Flatness is used only for the original higher-image base-change supplier. -/
theorem moduleCohomologyComparison_affineFlatBaseChange_unit
    {R T : CommRingCat.{u}} {X Y : Scheme.{u}}
    (a : Y ⟶ X) (b : Y ⟶ Spec T) (f : X ⟶ Spec R)
    [QuasiCompact f] [QuasiSeparated f] (φ : R ⟶ T) [Flat (Spec.map φ)]
    (h : IsPullback a b f (Spec.map φ)) (M : X.Modules) [M.IsQuasicoherent]
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((Scheme.Modules.pullback a).obj M)) (q : ℕ)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{e'} (AbelianSheaf.{u, u + 1} Y)]
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj M)) :
    let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
    moduleCohomologyComparison.{u, u + 1, e'} Y
        ((Scheme.Modules.pullback a).obj M) q
        (moduleHigherDirectImageAffineSectionsLinearEquiv b
          ((Scheme.Modules.pullback a).obj M) J q
          ((moduleSpecΓFunctor (R := T)).map
            ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f (Spec.map φ) h q).app M)
            ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
              (((Scheme.Modules.pushforward f).rightDerived q).obj M)).app ⊤) x))) =
      additiveCoefficientCohomologyPullback.{u, e, e'} a M q
        (moduleCohomologyComparison.{u, u + 1, e} X M q
          (moduleHigherDirectImageAffineSectionsLinearEquiv f M I q x)) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  have hb := moduleHigherDirectImageAffineSectionsLinearEquiv_flatBaseChange_unit
    a b f φ h M I J q x
  have hn := DFunLike.congr_fun (moduleCohomologyComparison_pullback.{u, e, e'} a M q)
    (moduleHigherDirectImageAffineSectionsLinearEquiv f M I q x)
  exact (congrArg (moduleCohomologyComparison.{u, u + 1, e'} Y
    ((Scheme.Modules.pullback a).obj M) q) hb).trans hn

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
