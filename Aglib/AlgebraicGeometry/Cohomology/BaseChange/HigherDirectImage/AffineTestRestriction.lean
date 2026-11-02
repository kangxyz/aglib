/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.AffineTestSections

/-! # Native higher-image sections for actual affine-test triangles

The section unit and the original flat base-change maps paste before any
cohomology comparison. Applying the original affine section comparison then
gives geometric pullback followed by the original module composition map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

open Scheme.Modules

attribute [local instance] HasExt.standard

variable {X S W Z : Scheme.{u}} {R T : CommRingCat.{u}}
  (a : W ⟶ X) (b : W ⟶ Spec R) (f : X ⟶ S) (j : Spec R ⟶ S)
  (h : IsPullback a b f j) (c : Z ⟶ W) (d : Z ⟶ Spec T) (φ : R ⟶ T)
  (h' : IsPullback c d b (Spec.map φ))
  [Flat j] [Flat (Spec.map φ)] (M : X.Modules) (q : ℕ)

include h' in
/-- Successive affine-test restriction of the original higher-image sections
is geometric cohomology pullback followed by the native module composition
map. Every comparison uses the supplied original injective resolutions. -/
theorem moduleHigherDirectImageAffineSections_flatBaseChange_triangle
    (a' : Z ⟶ X) (j' : Spec T ⟶ S)
    (H : IsPullback a' d f j') (ha : c ≫ a = a') (hj : Spec.map φ ≫ j = j')
    [Flat j'] [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent]
    (I : InjectiveResolution ((Scheme.Modules.pullback a).obj M))
    (J : InjectiveResolution ((Scheme.Modules.pullback c).obj
      ((Scheme.Modules.pullback a).obj M)))
    (K : InjectiveResolution ((Scheme.Modules.pullback a').obj M))
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M))) :
    let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiCompact d := MorphismProperty.of_isPullback H inferInstance
    let : QuasiSeparated d := MorphismProperty.of_isPullback H inferInstance
    moduleHigherDirectImageAffineSectionsLinearEquiv d
        ((Scheme.Modules.pullback a').obj M) K q
        ((moduleSpecΓFunctor (R := T)).map
          ((pullbackComp (Spec.map φ) j).hom.app
            (((Scheme.Modules.pushforward f).rightDerived q).obj M) ≫
          (pullbackCongr hj).hom.app
            (((Scheme.Modules.pushforward f).rightDerived q).obj M) ≫
          (higherDirectImageFlatBaseChangeMap a' d f j' H q).app M)
          ((((pullbackPushforwardAdjunction (Spec.map φ)).unit.app
            ((Scheme.Modules.pullback j).obj
              (((Scheme.Modules.pushforward f).rightDerived q).obj M))).app ⊤) x)) =
      Sheaf.H.map
        ((SheafOfModules.toSheaf Z.ringCatSheaf).map
          ((pullbackComp c a).hom.app M ≫ (pullbackCongr ha).hom.app M)) q
        (moduleCohomologyPullback c ((Scheme.Modules.pullback a).obj M) q
          (moduleHigherDirectImageAffineSectionsLinearEquiv b
            ((Scheme.Modules.pullback a).obj M) I q
            ((moduleSpecΓFunctor (R := R)).map
              ((higherDirectImageFlatBaseChangeMap a b f j h q).app M) x))) := by
  subst a'
  subst j'
  simpa only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Category.comp_id] using
    moduleHigherDirectImageAffineSections_flatBaseChange_comp
      a b f j h c d φ h' H M q I J K x

end AlgebraicGeometry.Scheme.Cohomology
