/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.AffineSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.UnitBaseChange
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCompositeCoefficient

/-! # Original affine-test comparison with native unit coefficients

For every actual pulled-back higher-image section, cancelling the original
étale coefficient isomorphism and applying the native unit comparison gives
the original unit-cohomology comparison of the native higher-image value.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry.Scheme.Cohomology

universe u e

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] HasExt.standard hasSheafifyLarge Scheme.Modules.isQuasicoherent_unit
  moduleComparisonEnoughSmall moduleComparisonEnoughRaised
  moduleComparisonAbWRaised moduleComparisonTypeWRaised

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
  {R : CommRingCat.{u}} (j : Spec R ⟶ S) [Etale j] (q : ℕ)
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (Limits.pullback j f))]

/-- Cancelling the actual étale coefficient map retains every original affine
higher-image and absolute cohomology comparison. -/
theorem higherDirectImageAffineSectionsEquiv_coefficient
    (M : X.Modules) [M.IsQuasicoherent]
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M))) :
    let a := Limits.pullback.snd j f
    let b := Limits.pullback.fst j f
    let h : IsPullback a b f j := (IsPullback.of_hasPullback j f).flip
    let N := (Scheme.Modules.pullback a).obj M
    @Eq (Sheaf.H.{e} (additiveCoefficient (Limits.pullback j f) N) q)
      (Sheaf.H.map (additiveCoefficientPullback a M) q
        (higherDirectImageAffineSectionsEquiv.{u, e} f j M q x))
      (moduleCohomologyComparison.{u, u + 1, e} (Limits.pullback j f) N q
        (moduleHigherDirectImageAffineSectionsLinearEquiv b N (injectiveResolution N) q
          ((moduleSpecΓFunctor (R := R)).map
            ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f j h q).app M) x))) := by
  let a := Limits.pullback.snd j f
  let b := Limits.pullback.fst j f
  let h : IsPullback a b f j := (IsPullback.of_hasPullback j f).flip
  let N := (Scheme.Modules.pullback a).obj M
  let eBC := (moduleSpecΓFunctor (R := R)).mapIso
    (Scheme.Modules.higherDirectImageFlatBaseChangeIso a b f j h M q)
  let := moduleCohomologyModuleOfHom (Limits.pullback j f)
    (b.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom) N q
  let eH := moduleHigherDirectImageAffineSectionsLinearEquiv b N (injectiveResolution N) q
  let eE := moduleCohomologyComparison.{u, u + 1, e} (Limits.pullback j f) N q
  let eβ := (asIso (additiveCoefficientPullback a M)).symm
  have hc := Sheaf.moduleCohomologyComposite_coefficient_inv q eBC eH eE eβ x
  have hm : eBC.hom x = (moduleSpecΓFunctor (R := R)).map
      ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f j h q).app M) x := by
    simp only [eBC, Functor.mapIso_hom,
      Scheme.Modules.higherDirectImageFlatBaseChangeIso_hom]
    rfl
  have hf := hc.trans (congrArg (fun z => eE (eH z)) hm)
  dsimp only
  exact hf

/-- Complete native coefficient comparison after cancelling the original
étale pullback coefficient, with arbitrary target module and morphism. -/
theorem higherDirectImageAffineSectionsEquiv_coefficientMap
    (M : X.Modules) [M.IsQuasicoherent]
    (N : (Limits.pullback j f).Modules) [N.IsQuasicoherent]
    (v : (Scheme.Modules.pullback (Limits.pullback.snd j f)).obj M ⟶ N)
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M))) :
    let a := Limits.pullback.snd j f
    let b := Limits.pullback.fst j f
    let h : IsPullback a b f j := (IsPullback.of_hasPullback j f).flip
    @Eq (Sheaf.H.{e} (additiveCoefficient (Limits.pullback j f) N) q)
      (Sheaf.H.map (additiveCoefficientMap (Limits.pullback j f) v) q
        (Sheaf.H.map (additiveCoefficientPullback a M) q
          (higherDirectImageAffineSectionsEquiv.{u, e} f j M q x)))
      (moduleCohomologyComparison.{u, u + 1, e} (Limits.pullback j f) N q
        (moduleHigherDirectImageAffineSectionsLinearEquiv b N (injectiveResolution N) q
          ((moduleSpecΓFunctor (R := R)).map
            (((Scheme.Modules.pushforward b).rightDerived q).map v)
            ((moduleSpecΓFunctor (R := R)).map
              ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f j h q).app M) x)))) := by
  let a := Limits.pullback.snd j f
  let b := Limits.pullback.fst j f
  let h : IsPullback a b f j := (IsPullback.of_hasPullback j f).flip
  let P := (Scheme.Modules.pullback a).obj M
  let z := (moduleSpecΓFunctor (R := R)).map
    ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f j h q).app M) x
  have hc := higherDirectImageAffineSectionsEquiv_coefficient.{u, e} f j q M x
  have hn := moduleCohomologyComparison_affineSections_naturality.{u, e} b v
    (injectiveResolution P) (injectiveResolution N) q z
  exact (congrArg (Sheaf.H.map (additiveCoefficientMap (Limits.pullback j f) v) q) hc).trans
    hn.symm

/-- Arbitrary original relative sections, not just geometric section units,
agree with the unchanged native unit-cohomology comparison. -/
theorem higherDirectImageAffineSectionsEquiv_unit
    (x : (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj
          (SheafOfModules.unit X.ringCatSheaf)))) :
    let Y := Limits.pullback j f
    let a := Limits.pullback.snd j f
    let b := Limits.pullback.fst j f
    let h : IsPullback a b f j := (IsPullback.of_hasPullback j f).flip
    @Eq (Sheaf.H.{e} (additiveCoefficient Y (SheafOfModules.unit Y.ringCatSheaf)) q)
      (Sheaf.H.map (additiveCoefficientMap Y (Scheme.Modules.pullbackUnitIso a).hom) q
        (Sheaf.H.map (additiveCoefficientPullback a (SheafOfModules.unit X.ringCatSheaf)) q
          (higherDirectImageAffineSectionsEquiv.{u, e} f j
            (SheafOfModules.unit X.ringCatSheaf) q x)))
      (higherDirectImageUnitCohomologyEquiv.{u, e} b q
        ((moduleSpecΓFunctor (R := R)).map
          (((Scheme.Modules.pushforward b).rightDerived q).map
            (Scheme.Modules.pullbackUnitIso a).hom)
          ((moduleSpecΓFunctor (R := R)).map
            ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f j h q).app
              (SheafOfModules.unit X.ringCatSheaf)) x))) := by
  let Y := Limits.pullback j f
  let a := Limits.pullback.snd j f
  let b := Limits.pullback.fst j f
  let h : IsPullback a b f j := (IsPullback.of_hasPullback j f).flip
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let N : Y.Modules := (Scheme.Modules.pullback a).obj O
  let P : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let v : N ⟶ P := (Scheme.Modules.pullbackUnitIso a).hom
  let z : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward b).rightDerived q).obj N) :=
    (moduleSpecΓFunctor (R := R)).map
      ((Scheme.Modules.higherDirectImageFlatBaseChangeMap a b f j h q).app O) x
  let y := (moduleSpecΓFunctor (R := R)).map
    (((Scheme.Modules.pushforward b).rightDerived q).map v) z
  have hc := higherDirectImageAffineSectionsEquiv_coefficientMap.{u, e} f j q O P v x
  have he := higherDirectImageUnitCohomologyEquiv_apply.{u, e} b q y
  have hf := hc.trans he.symm
  dsimp only [y, z, v, N, P, O, Y, a, b, h] at hf
  dsimp only
  exact hf

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
