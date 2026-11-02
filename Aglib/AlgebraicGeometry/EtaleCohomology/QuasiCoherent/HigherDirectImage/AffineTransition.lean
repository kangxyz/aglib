/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.AffineTestRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ModuleCohomologyNaturality

/-! # Original étale cohomology for affine-test transitions

The section unit and the original flat base-change maps paste before any
cohomology comparison. Applying the original affine section comparison then
gives geometric pullback followed by the original module composition map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u e e'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

open Scheme.Modules Scheme.Cohomology

attribute [local instance] HasExt.standard hasSheafifyLarge
  moduleComparisonEnoughSmall moduleComparisonEnoughRaised
  moduleComparisonAbWRaised moduleComparisonTypeWRaised

variable {X S W Z : Scheme.{u}} {R T : CommRingCat.{u}}
  (a : W ⟶ X) (b : W ⟶ Spec R) (f : X ⟶ S) (j : Spec R ⟶ S)
  (h : IsPullback a b f j) (c : Z ⟶ W) (d : Z ⟶ Spec T) (φ : R ⟶ T)
  (h' : IsPullback c d b (Spec.map φ))
  [Flat j] [Flat (Spec.map φ)] (M : X.Modules) (q : ℕ)

local instance [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback c).obj M).IsQuasicoherent :=
  inferInstanceAs (((Scheme.Modules.pullback c).obj
    ((Scheme.Modules.pullback a).obj M)).IsQuasicoherent)

include h' in
/-- Successive affine-test restriction of the original higher-image sections
is geometric cohomology pullback followed by the native module composition
map. Both absolute comparisons preserve their independent étale Ext ranges. -/
theorem moduleCohomologyComparison_affineFlatBaseChange_triangle
    (a' : Z ⟶ X) (j' : Spec T ⟶ S)
    (H : IsPullback a' d f j') (ha : c ≫ a = a') (hj : Spec.map φ ≫ j = j')
    [Flat j'] [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent]
    (I : InjectiveResolution ((Scheme.Modules.pullback a).obj M))
    (J : InjectiveResolution ((Scheme.Modules.pullback c).obj
      ((Scheme.Modules.pullback a).obj M)))
    (K : InjectiveResolution ((Scheme.Modules.pullback a').obj M))
    [HasExt.{e} (AbelianSheaf.{u, u + 1} W)]
    [HasExt.{e'} (AbelianSheaf.{u, u + 1} Z)]
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M))) :
    let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiCompact d := MorphismProperty.of_isPullback H inferInstance
    let : QuasiSeparated d := MorphismProperty.of_isPullback H inferInstance
    moduleCohomologyComparison.{u, u + 1, e'} Z
      ((Scheme.Modules.pullback a').obj M) q
      (moduleHigherDirectImageAffineSectionsLinearEquiv d
        ((Scheme.Modules.pullback a').obj M) K q
        ((moduleSpecΓFunctor (R := T)).map
          ((pullbackComp (Spec.map φ) j).hom.app
            (((Scheme.Modules.pushforward f).rightDerived q).obj M) ≫
          (pullbackCongr hj).hom.app
            (((Scheme.Modules.pushforward f).rightDerived q).obj M) ≫
          (higherDirectImageFlatBaseChangeMap a' d f j' H q).app M)
          ((((pullbackPushforwardAdjunction (Spec.map φ)).unit.app
            ((Scheme.Modules.pullback j).obj
              (((Scheme.Modules.pushforward f).rightDerived q).obj M))).app ⊤) x))) =
      Sheaf.H.map
        (additiveCoefficientMap Z
          ((pullbackComp c a).hom.app M ≫ (pullbackCongr ha).hom.app M)) q
        (additiveCoefficientCohomologyPullback.{u, e, e'} c
          ((Scheme.Modules.pullback a).obj M) q
          (moduleCohomologyComparison.{u, u + 1, e} W
            ((Scheme.Modules.pullback a).obj M) q
            (moduleHigherDirectImageAffineSectionsLinearEquiv b
            ((Scheme.Modules.pullback a).obj M) I q
            ((moduleSpecΓFunctor (R := R)).map
              ((higherDirectImageFlatBaseChangeMap a b f j h q).app M) x)))) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiCompact d := MorphismProperty.of_isPullback H inferInstance
  let : QuasiSeparated d := MorphismProperty.of_isPullback H inferInstance
  let t := (pullbackComp c a).hom.app M ≫ (pullbackCongr ha).hom.app M
  let x₀ := moduleHigherDirectImageAffineSectionsLinearEquiv b
    ((Scheme.Modules.pullback a).obj M) I q
    ((moduleSpecΓFunctor (R := R)).map
      ((higherDirectImageFlatBaseChangeMap a b f j h q).app M) x)
  have hb := moduleHigherDirectImageAffineSections_flatBaseChange_triangle
    a b f j h c d φ h' M q a' j' H ha hj I J K x
  have hc := moduleCohomologyComparison_naturality.{u, u + 1, e'} Z t q
    (moduleCohomologyPullback c ((Scheme.Modules.pullback a).obj M) q x₀)
  have hn := DFunLike.congr_fun
    (moduleCohomologyComparison_pullback.{u, e, e'} c
      ((Scheme.Modules.pullback a).obj M) q) x₀
  exact (congrArg (moduleCohomologyComparison.{u, u + 1, e'} Z
    ((Scheme.Modules.pullback a').obj M) q) hb).trans
      (hc.trans (congrArg (Sheaf.H.map (additiveCoefficientMap Z t) q) hn))

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
