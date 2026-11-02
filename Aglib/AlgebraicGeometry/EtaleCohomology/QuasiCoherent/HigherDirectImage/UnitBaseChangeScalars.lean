/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.UnitBaseChange

/-! # Original higher-image Frobenius on scalar section units

The pure-tensor scalar formula uses only the native linear section maps,
the proved geometric-unit equation and the constructed semilinear Frobenius.
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

variable {R T : CommRingCat.{u}} {X Y : Scheme.{u}}
  (a : Y ⟶ X) (b : Y ⟶ Spec T) (f : X ⟶ Spec R)
  [QuasiCompact f] [QuasiSeparated f] (φ : R ⟶ T) [Etale (Spec.map φ)]
  (h : IsPullback a b f (Spec.map φ)) (q : ℕ)
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{e'} (AbelianSheaf.{u, u + 1} Y)]

/-- Frobenius on scalar multiples of the original geometric section unit
commutes with the unchanged native base-change and derived unit maps. -/
theorem higherDirectImageFrobenius_flatBaseChange_smul_unit
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (r : T) (x : (moduleSpecΓFunctor (R := R)).obj
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
    let η : (moduleSpecΓFunctor (R := R)).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj
          (SheafOfModules.unit X.ringCatSheaf)) →
        (moduleSpecΓFunctor (R := T)).obj
          ((Scheme.Modules.pullback (Spec.map φ)).obj
            (((Scheme.Modules.pushforward f).rightDerived q).obj
              (SheafOfModules.unit X.ringCatSheaf))) :=
      fun x => (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
      (((Scheme.Modules.pushforward f).rightDerived q).obj
        (SheafOfModules.unit X.ringCatSheaf))).app ⊤) x
    @Eq ((moduleSpecΓFunctor (R := T)).obj
      (((Scheme.Modules.pushforward b).rightDerived q).obj
        (SheafOfModules.unit Y.ringCatSheaf)))
      (higherDirectImageFrobenius.{u, e'} b q p hp hT (D (B (r • η x))))
      (D (B ((r ^ p) • η (higherDirectImageFrobenius.{u, e} f q p hp hR x)))) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  dsimp only
  simp only [map_smul, map_smulₛₗ, RingHom.frobeniusOfPrimeCastEqZero_apply]
  have hu := higherDirectImageFrobenius_flatBaseChange_unit.{u, e, e'}
    a b f φ h q p hp hR x
  dsimp only at hu
  exact congrArg
    (α := (moduleSpecΓFunctor (R := T)).obj
      (((Scheme.Modules.pushforward b).rightDerived q).obj
        (SheafOfModules.unit Y.ringCatSheaf)))
    (β := (moduleSpecΓFunctor (R := T)).obj
      (((Scheme.Modules.pushforward b).rightDerived q).obj
        (SheafOfModules.unit Y.ringCatSheaf)))
    (fun z => (r ^ p) • z) hu.symm

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
