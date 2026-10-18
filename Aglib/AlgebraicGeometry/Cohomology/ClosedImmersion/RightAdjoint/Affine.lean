/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.RightAdjoint.Affine
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Injective
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Affine sections of the native derived closed right adjoint

The original ordinary affine comparison identifies sections of the sole
closed right adjoint with native scalar coinduction. Exact closed pushforward
makes that right adjoint preserve injectives; exact tilde makes original
affine sections preserve injectives. Their actual installed D+ functors
therefore give `RΓ_S (Ri! K) = RF(coinduction) (RΓ_R K)` for every bounded-below
module-sheaf object. The unit equation retains the original ordinary
comparison and both installed composite-derived units.

The four supplied derived-category size universes remain independent. No
quasicoherence, flatness, regularity, finiteness or Noetherian premise is
imposed, and no injective term is assumed quasicoherent. This statement uses
actual derived sections on both sides. Sheaf purity and localization of its
top line remain separate calculations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u a b v z
namespace AlgebraicGeometry.Scheme.Modules
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsClosedImmersion (Spec.map φ)]
  [HasDerivedCategory.{a} (Spec R).Modules]
  [HasDerivedCategory.{b} (Spec S).Modules]
  [HasDerivedCategory.{v} (ModuleCat.{u} R)]
  [HasDerivedCategory.{z} (ModuleCat.{u} S)]

/-- The original affine closed right adjoint computes native derived coinduction after RΓ. -/
def derivedClosedImmersionRightAdjointAffineIso :
    (closedImmersionRightAdjoint (Spec.map φ)).rightDerivedFunctorPlus ⋙
        (moduleSpecΓFunctor (R := S)).rightDerivedFunctorPlus ≅
      (moduleSpecΓFunctor (R := R)).rightDerivedFunctorPlus ⋙
        (ModuleCat.coextendScalars φ.hom).rightDerivedFunctorPlus :=
  ((closedImmersionRightAdjoint (Spec.map φ)).rightDerivedFunctorPlusCompIsoOfPreservesInjectives
      (moduleSpecΓFunctor (R := S))).symm ≪≫
    (closedImmersionRightAdjoint (Spec.map φ) ⋙
      moduleSpecΓFunctor (R := S)).rightDerivedFunctorPlusIso
        (closedImmersionRightAdjointAffineIso φ) ≪≫
    (moduleSpecΓFunctor (R := R)).rightDerivedFunctorPlusCompIsoOfPreservesInjectives
      (ModuleCat.coextendScalars φ.hom)

/-- The actual derived affine comparison retains the ordinary comparison and installed units. -/
@[reassoc]
theorem derivedClosedImmersionRightAdjointAffineIso_unit
    (K : CochainComplex.Plus (Spec R).Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit (closedImmersionRightAdjoint (Spec.map φ))
        (moduleSpecΓFunctor (R := S))).app K ≫
      (derivedClosedImmersionRightAdjointAffineIso φ).hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (closedImmersionRightAdjointAffineIso φ)).hom.app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (moduleSpecΓFunctor (R := R))
        (ModuleCat.coextendScalars φ.hom)).app K := by
  let F := closedImmersionRightAdjoint (Spec.map φ)
  let A := moduleSpecΓFunctor (R := S)
  let J := moduleSpecΓFunctor (R := R)
  let B := ModuleCat.coextendScalars φ.hom
  let eL := F.rightDerivedFunctorPlusCompIsoOfPreservesInjectives A
  let eM := (F ⋙ A).rightDerivedFunctorPlusIso (closedImmersionRightAdjointAffineIso φ)
  let eR := J.rightDerivedFunctorPlusCompIsoOfPreservesInjectives B
  have hL : (F ⋙ A).rightDerivedFunctorPlusUnit.app K ≫
      eL.hom.app (DerivedCategory.Plus.Q.obj K) =
      (Functor.rightDerivedFunctorPlusCompUnit F A).app K := by
    rw [Functor.rightDerivedFunctorPlusCompUnit_app]
    exact F.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app A K
  have hM := (F ⋙ A).rightDerivedFunctorPlusIso_hom_app
    (closedImmersionRightAdjointAffineIso φ) K
  have hR : (J ⋙ B).rightDerivedFunctorPlusUnit.app K ≫
      eR.hom.app (DerivedCategory.Plus.Q.obj K) =
      (Functor.rightDerivedFunctorPlusCompUnit J B).app K := by
    rw [Functor.rightDerivedFunctorPlusCompUnit_app]
    exact J.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app B K
  change (Functor.rightDerivedFunctorPlusCompUnit F A).app K ≫
    eL.inv.app (DerivedCategory.Plus.Q.obj K) ≫
      eM.hom.app (DerivedCategory.Plus.Q.obj K) ≫
        eR.hom.app (DerivedCategory.Plus.Q.obj K) = _
  rw [← hL]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, hM]
  simp only [Category.assoc]
  rw [hR]

end AlgebraicGeometry.Scheme.Modules
