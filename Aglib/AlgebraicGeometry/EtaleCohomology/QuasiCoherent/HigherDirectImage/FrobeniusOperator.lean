/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.UnitFrobenius
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ModuleCohomologyComparison
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Scalars
public import Aglib.LinearAlgebra.SemilinearConjugate

/-! # Frobenius on original affine higher-image sections

The module is the actual `moduleSpecΓFunctor` value of the native higher direct
image. Frobenius is the original additive étale cohomology map through the
unchanged affine and absolute comparisons. Its semilinearity is proved with
native scalar actions, without a transported module structure on étale H.
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

/-- Original affine higher-image sections compared to original unit-coefficient H. -/
def higherDirectImageUnitCohomologyEquiv :
    (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj
        (SheafOfModules.unit X.ringCatSheaf)) ≃+
    Sheaf.H.{e} (additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf)) q := by
  let O := SheafOfModules.unit X.ringCatSheaf
  letI := moduleCohomologyModuleOfHom X
    (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom) O q
  let E := moduleHigherDirectImageAffineSectionsLinearEquiv f O (injectiveResolution O) q
  exact E.toAddEquiv.trans (moduleCohomologyComparison.{u, u + 1, e} X O q)

/-- The original structural scalar is preserved as the original coefficient
multiplication map. No module action is installed on the étale cohomology group. -/
theorem higherDirectImageUnitCohomologyEquiv_smul (r : R)
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj
        (SheafOfModules.unit X.ringCatSheaf))) :
    higherDirectImageUnitCohomologyEquiv.{u, e} f q (r • x) =
      Sheaf.H.map (additiveCoefficientMap X
        (Scheme.Modules.unitMul X (f.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r)))) q
        (higherDirectImageUnitCohomologyEquiv.{u, e} f q x) := by
  let O := SheafOfModules.unit X.ringCatSheaf
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let := moduleCohomologyModuleOfHom X α O q
  let E := moduleHigherDirectImageAffineSectionsLinearEquiv f O (injectiveResolution O) q
  have hs := E.map_smul r x
  have hn := moduleCohomologyComparison_naturality.{u, u + 1, e} X
    (Scheme.Modules.unitMul X (α r)) q (E x)
  rw [moduleUnitMul_toAddSheaf] at hn
  exact (congrArg (moduleCohomologyComparison.{u, u + 1, e} X O q) hs).trans hn

include f in
omit [QuasiCompact f] [QuasiSeparated f] [HasExt.{e} (AbelianSheaf.{u, u + 1} X)] in
/-- Prime-cast vanishing on the affine base passes along its actual structure map. -/
theorem higherDirectImage_primeCast_source (p : ℕ) (hR : (p : R) = 0) :
    (p : Γ(X, ⊤)) = 0 := by
  have h := congrArg (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom) hR
  simpa only [map_natCast, map_zero] using h

/-- The actual semilinear Frobenius on the native affine higher-image module.
Its underlying additive map is the original Frobenius cohomology map under
the original comparisons; Frobenius is not asserted to be module-linear. -/
def higherDirectImageFrobenius (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) :
    (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj
        (SheafOfModules.unit X.ringCatSheaf)) →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hR]
    (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj
        (SheafOfModules.unit X.ringCatSheaf)) := by
  let E := higherDirectImageUnitCohomologyEquiv.{u, e} f q
  let hX := higherDirectImage_primeCast_source f p hR
  let F := Sheaf.H.map (unitFrobenius X p hp hX) q
  let A := fun r : R => Sheaf.H.map (additiveCoefficientMap X
    (Scheme.Modules.unitMul X (f.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r)))) q
  refine E.semilinearConjugate (RingHom.frobeniusOfPrimeCastEqZero p hp hR) A F
    (higherDirectImageUnitCohomologyEquiv_smul.{u, e} f q) ?_
  intro r y
  have h := congrArg (fun k => Sheaf.H.map k q y)
    (unitFrobenius_unitMul X p hp hX (f.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r)))
  simpa only [A, F, Sheaf.H.map_comp_apply,
    RingHom.frobeniusOfPrimeCastEqZero_apply, map_pow] using h

/-- The constructed semilinear map retains the original Frobenius cohomology map. -/
theorem higherDirectImageFrobenius_apply (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj
        (SheafOfModules.unit X.ringCatSheaf))) :
    @Eq (Sheaf.H.{e} (additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf)) q)
      (higherDirectImageUnitCohomologyEquiv.{u, e} f q
        (higherDirectImageFrobenius.{u, e} f q p hp hR x))
      (Sheaf.H.map (unitFrobenius X p hp (higherDirectImage_primeCast_source f p hR)) q
        (higherDirectImageUnitCohomologyEquiv.{u, e} f q x)) := by
  unfold higherDirectImageFrobenius
  apply AddEquiv.semilinearConjugate_apply
    (higherDirectImageUnitCohomologyEquiv.{u, e} f q)
    (RingHom.frobeniusOfPrimeCastEqZero p hp hR)
    (fun r : R => Sheaf.H.map (additiveCoefficientMap X
      (Scheme.Modules.unitMul X (f.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r)))) q)
    (Sheaf.H.map (unitFrobenius X p hp (higherDirectImage_primeCast_source f p hR)) q)
    (higherDirectImageUnitCohomologyEquiv_smul.{u, e} f q) _ x

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
