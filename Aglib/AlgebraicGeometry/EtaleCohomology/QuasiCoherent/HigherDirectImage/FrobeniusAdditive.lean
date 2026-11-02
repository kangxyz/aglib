/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.HigherDirectImage.FrobeniusOperator

/-! # Original additive view of native higher-image Frobenius

The existing semilinear map's native additive projection retains its original
values and cohomology intertwining law. No alternate operator is constructed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry.Scheme.Cohomology

universe u e

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] HasExt.standard hasSheafifyLarge Scheme.Modules.isQuasicoherent_unit
  moduleComparisonEnoughSmall moduleComparisonEnoughRaised
  moduleComparisonAbWRaised moduleComparisonTypeWRaised

variable {R : CommRingCat.{u}} {X : Scheme.{u}}
  (f : X ⟶ Spec R) [QuasiCompact f] [QuasiSeparated f] (q : ℕ)
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]

/-- The native additive projection retains the original semilinear value. -/
theorem higherDirectImageFrobenius_toAddMonoidHom_apply
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj
        (SheafOfModules.unit X.ringCatSheaf))) :
    @Eq ((moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj
        (SheafOfModules.unit X.ringCatSheaf)))
      ((higherDirectImageFrobenius.{u, e} f q p hp hR).toAddMonoidHom x)
      (higherDirectImageFrobenius.{u, e} f q p hp hR x) :=
  congrFun (LinearMap.toAddMonoidHom_coe
    (higherDirectImageFrobenius.{u, e} f q p hp hR)) x

/-- The same native additive projection has the original unit-cohomology action. -/
theorem higherDirectImageFrobenius_toAddMonoidHom_cohomology
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj
        (SheafOfModules.unit X.ringCatSheaf))) :
    @Eq (Sheaf.H.{e} (additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf)) q)
      (higherDirectImageUnitCohomologyEquiv.{u, e} f q
        ((higherDirectImageFrobenius.{u, e} f q p hp hR).toAddMonoidHom x))
      (Sheaf.H.map (unitFrobenius X p hp (higherDirectImage_primeCast_source f p hR)) q
        (higherDirectImageUnitCohomologyEquiv.{u, e} f q x)) :=
  (congrArg (higherDirectImageUnitCohomologyEquiv.{u, e} f q)
    (higherDirectImageFrobenius_toAddMonoidHom_apply.{u, e} f q p hp hR x)).trans
      (higherDirectImageFrobenius_apply.{u, e} f q p hp hR x)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
