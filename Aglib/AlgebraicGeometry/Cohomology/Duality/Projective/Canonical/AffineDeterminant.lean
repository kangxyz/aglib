/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalPurity
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Algebra
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The affine canonical map from the actual conormal determinant

The ambient differential basis gives the original exterior coefficient
frame and its pulled-back frame. The base change of that same basis frames
the top exterior power of the actual conormal middle term. These frames
compare the same ambient determinant with the pulled-back coefficient;
the normal-first conormal determinant and native evaluation then supply the
local canonical map of the installed right adjoint.

Only the local dimension equality is used: the ambient basis has degree
`s.length + d`. The chart supplier must derive that equality at its chosen
point before applying this construction. No dimension inequality is imposed
on an empty global source.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u w a b
namespace AlgebraicGeometry.Scheme.Modules

variable {R A : CommRingCat.{u}} (α : R ⟶ A)

/-- The actual ambient top exterior sheaf framed by the supplied ordered differential basis. -/
def affineRelativeTopFrame (n : ℕ)
    (bA : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α)) :
    moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) n ≅
      SheafOfModules.unit (Spec A).ringCatSheaf :=
  (moduleExteriorPowerFunctor (Spec A) n).mapIso
    (relativeDifferentialAffineIso α ≪≫
      tildeBasisIso (CommRingCat.KaehlerDifferential α) (bA.reindex Equiv.ulift.symm)) ≪≫
    SheafOfModulesOfCommRing.exteriorTopFreeIso (Spec A).sheaf n

private def affineRelativeTopSectionsFrame (n : ℕ)
    (bA : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α)) :
    moduleSpecΓFunctor.obj
      (moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) n) ≅
        ModuleCat.of A A :=
  moduleSpecΓFunctor.mapIso (affineRelativeTopFrame α n bA) ≪≫
    moduleSpecΓFunctor.mapIso (tildeSelf (R := A)).symm ≪≫
    (tilde.toTildeΓNatIso (R := A)).symm.app (ModuleCat.of A A)

private theorem affineRelativeTop_quasicoherent (n : ℕ)
    (bA : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α)) :
    (moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) n).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).prop_of_iso
    (tildeSelf ≪≫ (affineRelativeTopFrame α n bA).symm) inferInstance

variable (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s)

/-- The original ambient differential basis after native extension of scalars. -/
def affineConormalAmbientBaseChangedBasis (n : ℕ)
    (bA : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α)) :
    Module.Basis (Fin n) ((regularListQuotientRing s))
      ((ModuleCat.extendScalars (regularListQuotientMap s).hom).obj
        (CommRingCat.KaehlerDifferential α)) := by
  letI := (regularListQuotientMap s).hom.toAlgebra
  exact (bA.baseChange ((regularListQuotientRing s))).map
    ((ModuleCat.extendScalarsAlgebraObjIso A ((regularListQuotientRing s))
      (CommRingCat.KaehlerDifferential α)).symm.toLinearEquiv)

/-- The native top-free frame of the actual base-changed ambient differential sheaf. -/
def affineConormalAmbientMiddleTopFrame (n : ℕ)
    (bA : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α)) :
    moduleExteriorPower (Spec ((regularListQuotientRing s)))
      ((pullback (Spec.map (regularListQuotientMap s))).obj
        (relativeDifferentialSheaf (Spec.map α))) n ≅
      SheafOfModules.unit (Spec ((regularListQuotientRing s))).ringCatSheaf :=
  (moduleExteriorPowerFunctor (Spec ((regularListQuotientRing s))) n).mapIso
    (relativeConormalAffineMiddleIso α (regularListQuotientMap s) ≪≫
      tildeBasisIso _
        ((affineConormalAmbientBaseChangedBasis α s n bA).reindex Equiv.ulift.symm)) ≪≫
    SheafOfModulesOfCommRing.exteriorTopFreeIso (Spec ((regularListQuotientRing s))).sheaf n

/-- The same ambient basis compares its base-changed determinant with the pulled-back top
coefficient. Its maps retain the original affine differential and pullback comparisons. -/
def affineConormalAmbientCoefficientIso (n : ℕ)
    (bA : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential α)) :
    moduleExteriorPower (Spec ((regularListQuotientRing s)))
      ((pullback (Spec.map (regularListQuotientMap s))).obj
        (relativeDifferentialSheaf (Spec.map α))) n ≅
      (pullback (Spec.map (regularListQuotientMap s))).obj
        (moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α)) n) :=
  affineConormalAmbientMiddleTopFrame α s n bA ≪≫
    ((pullback (Spec.map (regularListQuotientMap s))).mapIso (affineRelativeTopFrame α n bA) ≪≫
      pullbackUnitIso (Spec.map (regularListQuotientMap s))).symm

variable (hA : α.hom.FormallySmooth)
  (hB : (α ≫ (regularListQuotientMap s)).hom.FormallySmooth) {d : ℕ}
  (bA : Module.Basis (Fin (s.length + d)) A (CommRingCat.KaehlerDifferential α))
  (bQ : Module.Basis (Fin d) ((regularListQuotientRing s))
    (CommRingCat.KaehlerDifferential (α ≫ (regularListQuotientMap s))))

/-- The same actual normal-first conormal determinant, with its original ambient coefficient. -/
@[no_expose] def affineRegularListCanonicalDeterminant :
    tensorSheaf (Spec ((regularListQuotientRing s)))
      (closedImmersionRegularListNormalLineBundle α s hs).val
      (moduleExteriorPower (Spec ((regularListQuotientRing s)))
        (relativeDifferentialSheaf (Spec.map (α ≫ (regularListQuotientMap s)))) d) ≅
      (pullback (Spec.map (regularListQuotientMap s))).obj
        (moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α))
          (s.length + d)) :=
  relativeConormalAffineDeterminantIso α (regularListQuotientMap s) Ideal.Quotient.mk_surjective
    s hs Ideal.mk_ker.symm hA hB bQ ≪≫
      affineConormalAmbientCoefficientIso α s (s.length + d) bA

/-- The local determinant is the original normal-first determinant and the same ambient
coefficient comparison, with their actual maps. -/
theorem affineRegularListCanonicalDeterminant_eq :
    affineRegularListCanonicalDeterminant α s hs hA hB bA bQ =
      relativeConormalAffineDeterminantIso α (regularListQuotientMap s)
        Ideal.Quotient.mk_surjective s hs Ideal.mk_ker.symm hA hB bQ ≪≫
          affineConormalAmbientCoefficientIso α s (s.length + d) bA := by
  rfl

variable [HasExt.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{a} (Spec A).Modules]
  [HasDerivedCategory.{b} (Spec ((regularListQuotientRing s))).Modules]

/-- Actual affine regular-list canonical purity. The determinant and coefficient frame are
constructed from the supplied actual differential bases, rather than assumed as comparisons. -/
@[no_expose] def affineRegularListCanonicalIso :
    (closedImmersionRightAdjoint (Spec.map (regularListQuotientMap s))).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (Spec A).Modules 0).obj
        (moduleExteriorPower (Spec A) (relativeDifferentialSheaf (Spec.map α))
          (s.length + d))) ≅
      (DerivedCategory.Plus.singleFunctor (Spec ((regularListQuotientRing s))).Modules
        (s.length : ℤ)).obj
        (moduleExteriorPower (Spec ((regularListQuotientRing s)))
          (relativeDifferentialSheaf (Spec.map (α ≫ (regularListQuotientMap s)))) d) := by
  let := affineRelativeTop_quasicoherent α (s.length + d) bA
  exact derivedClosedImmersionRegularListCanonicalIso α s hs
    (affineRelativeTopSectionsFrame α (s.length + d) bA)
    (affineRegularListCanonicalDeterminant α s hs hA hB bA bQ)

end AlgebraicGeometry.Scheme.Modules
