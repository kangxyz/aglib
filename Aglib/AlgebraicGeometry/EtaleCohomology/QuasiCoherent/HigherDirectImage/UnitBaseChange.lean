/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.AffineBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.FrobeniusOperator
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.UnitFrobeniusCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.AffineCoefficientBaseChange

/-! # Unit-coefficient Frobenius and original affine base change

The original flat higher-image map, followed by the derived native unit
comparison, preserves Frobenius on geometric section units. No geometric
Frobenius flatness or replacement cohomology comparison is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry.Scheme.Cohomology

universe u e e'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] HasExt.standard hasSheafifyLarge Scheme.Modules.isQuasicoherent_unit
  moduleComparisonEnoughSmall moduleComparisonEnoughRaised
  moduleComparisonAbWRaised moduleComparisonTypeWRaised

/-- Whole evaluation of the original additive composite, before base change. -/
theorem higherDirectImageUnitCohomologyEquiv_apply
    {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [QuasiCompact f] [QuasiSeparated f] (q : ℕ)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj
        (SheafOfModules.unit X.ringCatSheaf))) :
    @Eq (Sheaf.H.{e} (additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf)) q)
      (higherDirectImageUnitCohomologyEquiv.{u, e} f q x)
      (moduleCohomologyComparison.{u, u + 1, e} X
        (SheafOfModules.unit X.ringCatSheaf) q
        (moduleHigherDirectImageAffineSectionsLinearEquiv f
          (SheafOfModules.unit X.ringCatSheaf)
          (injectiveResolution (SheafOfModules.unit X.ringCatSheaf)) q x)) := by
  unfold higherDirectImageUnitCohomologyEquiv
  exact AddEquiv.trans_apply _ _ x

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}
  (a : Y ⟶ X) (b : Y ⟶ Spec T) (f : X ⟶ Spec R)
  [QuasiCompact f] [QuasiSeparated f] (φ : R ⟶ T) [Etale (Spec.map φ)]
  (h : IsPullback a b f (Spec.map φ)) (q : ℕ)
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{e'} (AbelianSheaf.{u, u + 1} Y)]

/-- The unchanged unit-coefficient comparison takes native higher-image base
change on the section unit to original geometric coefficient pullback. -/
theorem higherDirectImageUnitCohomologyEquiv_flatBaseChange_unit
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj
        (SheafOfModules.unit X.ringCatSheaf))) :
    let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
    @Eq (Sheaf.H.{e'}
      (additiveCoefficient Y (SheafOfModules.unit Y.ringCatSheaf)) q)
    (higherDirectImageUnitCohomologyEquiv.{u, e'} b q
      ((moduleSpecΓFunctor (R := T)).map
        (((Scheme.Modules.pushforward b).rightDerived q).map
          (Scheme.Modules.pullbackUnitIso a).hom)
        ((moduleSpecΓFunctor (R := T)).map
          ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f (Spec.map φ) h q).app
            (SheafOfModules.unit X.ringCatSheaf))
          ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
            (((Scheme.Modules.pushforward f).rightDerived q).obj
              (SheafOfModules.unit X.ringCatSheaf))).app ⊤) x))))
    (Sheaf.H.map (additiveCoefficientMap Y (Scheme.Modules.pullbackUnitIso a).hom) q
      (additiveCoefficientCohomologyPullback.{u, e, e'} a
        (SheafOfModules.unit X.ringCatSheaf) q
        (higherDirectImageUnitCohomologyEquiv.{u, e} f q x))) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let N : Y.Modules := (Scheme.Modules.pullback a).obj O
  let P : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let v : N ⟶ P := (Scheme.Modules.pullbackUnitIso a).hom
  let z : (moduleSpecΓFunctor (R := T)).obj
      (((Scheme.Modules.pushforward b).rightDerived q).obj N) :=
    (moduleSpecΓFunctor (R := T)).map
    ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f (Spec.map φ) h q).app O)
    ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
      (((Scheme.Modules.pushforward f).rightDerived q).obj O)).app ⊤) x)
  have hc := moduleCohomologyComparison_affineFlatBaseChange_coefficient_unit.{u, e, e'}
    a b f φ h O P v (injectiveResolution O) (injectiveResolution N)
    (injectiveResolution P) q x
  let y : (moduleSpecΓFunctor (R := T)).obj
      (((Scheme.Modules.pushforward b).rightDerived q).obj P) :=
    (moduleSpecΓFunctor (R := T)).map
    (((Scheme.Modules.pushforward b).rightDerived q).map v) z
  have he := higherDirectImageUnitCohomologyEquiv_apply.{u, e'} b q y
  have hf := higherDirectImageUnitCohomologyEquiv_apply.{u, e} f q x
  have hs := congrArg (fun w => Sheaf.H.map (additiveCoefficientMap Y v) q
    (additiveCoefficientCohomologyPullback.{u, e, e'} a O q w)) hf
  have hcts := hc.trans hs.symm
  have hfull := he.trans hcts
  dsimp only [y, z, v, N, O, P] at hfull
  dsimp only
  exact hfull

/-- Frobenius commutes with the actual flat higher-image map on the original
geometric section unit, after the native derived pullback-unit comparison. -/
theorem higherDirectImageFrobenius_flatBaseChange_unit
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj
        (SheafOfModules.unit X.ringCatSheaf))) :
    let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
    let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
    let hT : (p : T) = 0 := by
      simpa only [map_natCast, map_zero] using congrArg φ.hom hR
    let D := (moduleSpecΓFunctor (R := T)).map
      (((Scheme.Modules.pushforward b).rightDerived q).map
        (Scheme.Modules.pullbackUnitIso a).hom)
    let B := (moduleSpecΓFunctor (R := T)).map
      ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f (Spec.map φ) h q).app
        (SheafOfModules.unit X.ringCatSheaf))
    let η := (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
      (((Scheme.Modules.pushforward f).rightDerived q).obj
        (SheafOfModules.unit X.ringCatSheaf))).app ⊤)
    D (B (η (higherDirectImageFrobenius.{u, e} f q p hp hR x))) =
      higherDirectImageFrobenius.{u, e'} b q p hp hT (D (B (η x))) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  let : Etale a := MorphismProperty.of_isPullback h.flip inferInstance
  let hT : (p : T) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg φ.hom hR
  dsimp only
  apply (higherDirectImageUnitCohomologyEquiv.{u, e'} b q).injective
  rw [higherDirectImageUnitCohomologyEquiv_flatBaseChange_unit,
    higherDirectImageFrobenius_apply, higherDirectImageFrobenius_apply,
    higherDirectImageUnitCohomologyEquiv_flatBaseChange_unit]
  exact unitFrobenius_cohomologyPullback.{u, e, e'} a p hp
    (higherDirectImage_primeCast_source f p hR)
    (higherDirectImage_primeCast_source b p hT) q
    (higherDirectImageUnitCohomologyEquiv.{u, e} f q x)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
