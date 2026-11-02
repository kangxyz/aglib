/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.FlatComparison.Composition
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.FlatComparison.Affine
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.Naturality

/-! # Native higher-image sections under successive affine tests

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
  (H : IsPullback (c ≫ a) d f (Spec.map φ ≫ j))
  [Flat j] [Flat (Spec.map φ)] (M : X.Modules) (q : ℕ)

/-- The original section-unit formula for pasting the actual higher-image
base-change maps. No quasicoherence or finiteness enters this map equation. -/
theorem higherDirectImageFlatBaseChange_sectionsUnit_comp
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M))) :
    (moduleSpecΓFunctor (R := T)).map
        ((pullbackComp (Spec.map φ) j).hom.app
          (((Scheme.Modules.pushforward f).rightDerived q).obj M) ≫
        (higherDirectImageFlatBaseChangeMap (c ≫ a) d f
          (Spec.map φ ≫ j) H q).app M)
        ((((pullbackPushforwardAdjunction (Spec.map φ)).unit.app
          ((Scheme.Modules.pullback j).obj
            (((Scheme.Modules.pushforward f).rightDerived q).obj M))).app ⊤) x) =
      (moduleSpecΓFunctor (R := T)).map
        ((higherDirectImageFlatBaseChangeMap c d b (Spec.map φ) h' q).app
          ((Scheme.Modules.pullback a).obj M) ≫
          ((Scheme.Modules.pushforward d).rightDerived q).map
            ((pullbackComp c a).hom.app M))
        ((((pullbackPushforwardAdjunction (Spec.map φ)).unit.app
          (((Scheme.Modules.pushforward b).rightDerived q).obj
            ((Scheme.Modules.pullback a).obj M))).app ⊤)
          ((moduleSpecΓFunctor (R := R)).map
            ((higherDirectImageFlatBaseChangeMap a b f j h q).app M) x)) := by
  rw [higherDirectImageFlatBaseChangeMap_comp a b f j h c d (Spec.map φ) h' H]
  rw [Functor.map_comp]
  change (moduleSpecΓFunctor (R := T)).map
      ((higherDirectImageFlatBaseChangeMap c d b (Spec.map φ) h' q).app
        ((Scheme.Modules.pullback a).obj M) ≫
        ((Scheme.Modules.pushforward d).rightDerived q).map
          ((pullbackComp c a).hom.app M))
      ((moduleSpecΓFunctor (R := T)).map
      ((Scheme.Modules.pullback (Spec.map φ)).map
        ((higherDirectImageFlatBaseChangeMap a b f j h q).app M)) _) = _
  congr 1
  have hu := (pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality
    ((higherDirectImageFlatBaseChangeMap a b f j h q).app M)
  exact (congrArg (fun k => (k.app ⊤) x) hu).symm


include h' in
/-- Successive affine-test restriction of the original higher-image sections
is geometric cohomology pullback followed by the native module composition
map. Every comparison uses the supplied original injective resolutions. -/
theorem moduleHigherDirectImageAffineSections_flatBaseChange_comp
    [QuasiCompact f] [QuasiSeparated f] [M.IsQuasicoherent]
    (I : InjectiveResolution ((Scheme.Modules.pullback a).obj M))
    (J : InjectiveResolution ((Scheme.Modules.pullback c).obj
      ((Scheme.Modules.pullback a).obj M)))
    (K : InjectiveResolution ((Scheme.Modules.pullback (c ≫ a)).obj M))
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M))) :
    let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiCompact d := MorphismProperty.of_isPullback H inferInstance
    let : QuasiSeparated d := MorphismProperty.of_isPullback H inferInstance
    moduleHigherDirectImageAffineSectionsLinearEquiv d
        ((Scheme.Modules.pullback (c ≫ a)).obj M) K q
        ((moduleSpecΓFunctor (R := T)).map
          ((pullbackComp (Spec.map φ) j).hom.app
            (((Scheme.Modules.pushforward f).rightDerived q).obj M) ≫
          (higherDirectImageFlatBaseChangeMap (c ≫ a) d f
            (Spec.map φ ≫ j) H q).app M)
          ((((pullbackPushforwardAdjunction (Spec.map φ)).unit.app
            ((Scheme.Modules.pullback j).obj
              (((Scheme.Modules.pushforward f).rightDerived q).obj M))).app ⊤) x)) =
      Sheaf.H.map
        ((SheafOfModules.toSheaf Z.ringCatSheaf).map ((pullbackComp c a).hom.app M)) q
        (moduleCohomologyPullback c ((Scheme.Modules.pullback a).obj M) q
          (moduleHigherDirectImageAffineSectionsLinearEquiv b
            ((Scheme.Modules.pullback a).obj M) I q
            ((moduleSpecΓFunctor (R := R)).map
              ((higherDirectImageFlatBaseChangeMap a b f j h q).app M) x))) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiCompact d := MorphismProperty.of_isPullback H inferInstance
  let : QuasiSeparated d := MorphismProperty.of_isPullback H inferInstance
  rw [higherDirectImageFlatBaseChange_sectionsUnit_comp a b f j h c d φ h' H]
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  let y := (moduleSpecΓFunctor (R := R)).map
    ((higherDirectImageFlatBaseChangeMap a b f j h q).app M) x
  let z := (moduleSpecΓFunctor (R := T)).map
    ((higherDirectImageFlatBaseChangeMap c d b (Spec.map φ) h' q).app
      ((Scheme.Modules.pullback a).obj M))
    ((((pullbackPushforwardAdjunction (Spec.map φ)).unit.app
      (((Scheme.Modules.pushforward b).rightDerived q).obj
        ((Scheme.Modules.pullback a).obj M))).app ⊤) y)
  have hc := moduleHigherDirectImageAffineSectionsLinearEquiv_naturality d J K
    (v := (pullbackComp c a).hom.app M) q z
  have hb := moduleHigherDirectImageAffineSectionsLinearEquiv_flatBaseChange_unit
    c d b φ h' ((Scheme.Modules.pullback a).obj M) I J q y
  exact hc.trans (congrArg
    (Sheaf.H.map ((SheafOfModules.toSheaf Z.ringCatSheaf).map
      ((pullbackComp c a).hom.app M)) q) hb)

end AlgebraicGeometry.Scheme.Cohomology
