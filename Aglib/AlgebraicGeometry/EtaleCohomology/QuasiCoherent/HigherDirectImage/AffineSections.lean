/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ModuleCohomologyNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.EtalePullback
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.QuasiCoherent
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleComposite

/-! # Actual higher-image sections on an affine étale test

The forward comparison uses the original native flat base-change map, the
original affine section/cohomology comparison, the unchanged absolute étale
comparison, and the inverse of the actual étale coefficient pullback arrow.
No properness, Noetherian hypothesis or replacement cohomology model occurs.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry.Scheme.Cohomology

universe u e

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] HasExt.standard hasSheafifyLarge
  moduleComparisonEnoughSmall moduleComparisonEnoughRaised
  moduleComparisonAbWRaised moduleComparisonTypeWRaised

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
  {R : CommRingCat.{u}} (j : Spec R ⟶ S) [Etale j]
  (M : X.Modules) [M.IsQuasicoherent] (q : ℕ)
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (Limits.pullback j f))]

/-- The comparison on original native sections over a literal affine étale
test. Its target is the original cohomology of the actual inverse-image
coefficient, not an identified or resized substitute. -/
def higherDirectImageAffineSectionsEquiv :
    (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pullback j).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj M)) ≃+
    Sheaf.H.{e}
      ((inverseImage (Limits.pullback.snd j f)).obj (additiveCoefficient X M)) q := by
  let a := Limits.pullback.snd j f
  let b := Limits.pullback.fst j f
  let h : IsPullback a b f j := (IsPullback.of_hasPullback j f).flip
  let : QuasiCompact b := inferInstance
  let : QuasiSeparated b := inferInstance
  let N := (Scheme.Modules.pullback a).obj M
  let eBC := (moduleSpecΓFunctor (R := R)).mapIso
    (Scheme.Modules.higherDirectImageFlatBaseChangeIso a b f j h M q)
  letI := moduleCohomologyModuleOfHom (Limits.pullback j f)
    (b.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom) N q
  let eH := moduleHigherDirectImageAffineSectionsLinearEquiv b N
    (injectiveResolution N) q
  let eE := moduleCohomologyComparison.{u, u + 1, e} (Limits.pullback j f) N q
  let eβ := (asIso (additiveCoefficientPullback a M)).symm
  exact Sheaf.moduleCohomologyComposite q eBC eH eE eβ

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
