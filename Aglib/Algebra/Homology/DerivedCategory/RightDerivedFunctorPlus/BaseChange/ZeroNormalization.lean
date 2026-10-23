/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Mathlib.Algebra.Homology.SingleHomology

/-! # Degree-zero normalization of the native bounded-below derived unit

The original plus-derived unit on a single induces the original transformation
to the zeroth right-derived functor, with all native comparison maps retained.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v u' v' w w'

namespace CategoryTheory.InjectiveResolution

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  (F : A ⥤ B) [F.Additive] {M : A} (I : InjectiveResolution M)

/-- The single-to-resolution map carries the original coefficient to the actual
integer-resolution cycle used by `toRightDerivedZero`. -/
private theorem single_cycles_augmentation :
    (singleObjCyclesSelfIso (.up ℤ) 0 (F.obj M)).inv ≫
      cyclesMap ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) 0 ≫
      cyclesMap ((F.mapHomologicalComplex (.up ℤ)).map I.ι') 0 =
    I.toRightDerivedZeroCochainCycles F := by
  apply (cancel_mono
    (((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).iCycles 0)).mp
  simp only [Category.assoc, cyclesMap_i,
    toRightDerivedZeroCochainCycles_comp_iCycles]
  erw [cyclesMap_i_assoc, singleObjCyclesSelfIso_inv_iCycles_assoc]
  change (singleObjXSelf (.up ℤ) 0 (F.obj M)).inv ≫
      ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M).f 0 ≫
        F.map (I.ι'.f 0) = _
  rw [singleMapHomologicalComplex_inv_app_self, I.ι'_f_zero]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]

/-- Homology of the mapped augmentation gives the original zero-derived cycle
projection, with the native single-complex comparison retained. -/
private theorem single_homology_augmentation :
    (singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).inv ≫
      homologyMap ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) 0 ≫
      homologyMap ((F.mapHomologicalComplex (.up ℤ)).map I.ι') 0 =
    I.toRightDerivedZeroCochainCycles F ≫
      ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homologyπ 0 := by
  rw [← singleObjCyclesSelfIso_inv_homologyπ]
  simp only [Category.assoc, homologyπ_naturality, homologyπ_naturality_assoc]
  have h := congrArg (fun k => k ≫
    ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homologyπ 0)
      (single_cycles_augmentation F I)
  simpa only [Category.assoc] using h

end CategoryTheory.InjectiveResolution

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w'} B] (F : A ⥤ B) [F.Additive]

/-- The actual plus-derived unit on a single induces the original transformation
to the zeroth right-derived functor under the native homology comparison.
No exactness or preservation of injectives is assumed. -/
theorem rightDerivedSingleHomologyIso_unit_zero (M : A) :
    F.toRightDerivedZero.app M ≫ (F.rightDerivedSingleHomologyIso 0).hom.app M =
      (singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).inv ≫
        homologyMap ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) 0 ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := B) 0).inv.app
          (F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus A 0).obj M)) ≫
        (DerivedCategory.Plus.homologyFunctor B 0).map
          (F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus A 0).obj M)) := by
  let I := injectiveResolution M
  let S := F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus A 0).obj M)
  let K := F.mapCochainComplexPlus.obj I.cochainComplexPlus
  let P₀ := (DerivedCategory.Plus.homologyFunctorFactors (A := B) 0).app S
  let P₁ := (DerivedCategory.Plus.homologyFunctorFactors (A := B) 0).app K
  let a := F.mapCochainComplexPlus.map I.ιPlus
  let H := DerivedCategory.Plus.homologyFunctor B 0
  have hP : P₀.inv ≫ H.map (DerivedCategory.Plus.Q.map a) =
      homologyMap ((F.mapHomologicalComplex (.up ℤ)).map I.ι') 0 ≫ P₁.inv := by
    apply (cancel_mono P₁.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have h := (DerivedCategory.Plus.homologyFunctorFactors (A := B) 0).hom.naturality a
    change H.map (DerivedCategory.Plus.Q.map a) ≫ P₁.hom =
      P₀.hom ≫ homologyMap ((F.mapHomologicalComplex (.up ℤ)).map I.ι') 0 at h
    rw [h]
    simp only [Iso.inv_hom_id_assoc]
  have hU := congrArg H.map (I.rightDerivedFunctorPlusIso_unit F)
  simp only [Functor.map_comp] at hU
  change H.map (DerivedCategory.Plus.Q.map a) ≫ H.map (I.rightDerivedFunctorPlusIso F).hom =
    H.map (F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus A 0).obj M)) at hU
  rw [F.rightDerivedSingleHomologyIso_hom_app I 0,
    InjectiveResolution.isoRightDerivedSingleHomology_hom]
  change F.toRightDerivedZero.app M ≫ (I.isoRightDerivedObjCochain F 0).hom ≫
      P₁.inv ≫ H.map (I.rightDerivedFunctorPlusIso F).hom =
    (singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).inv ≫
      homologyMap ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) 0 ≫
      P₀.inv ≫ H.map (F.rightDerivedFunctorPlusUnit.app
        ((CochainComplex.singleFunctorPlus A 0).obj M))
  rw [← hU, ← Category.assoc P₀.inv, hP]
  simp only [Category.assoc]
  rw [I.toRightDerivedZero_comp_isoRightDerivedObjCochain_assoc F]
  have hA := congrArg (fun k => k ≫ P₁.inv ≫ H.map (I.rightDerivedFunctorPlusIso F).hom)
    (InjectiveResolution.single_homology_augmentation F I)
  simpa only [Category.assoc] using hA.symm

/-- For left-exact functors the same literal unit is the inverse of the native
zeroth-homology comparison. Left exactness is used only for this invertibility. -/
theorem rightDerivedSingleHomologyZeroIso_inv_unit [PreservesFiniteLimits F] (M : A) :
    (F.rightDerivedSingleHomologyZeroIso).inv.app M =
      (singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).inv ≫
        homologyMap ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) 0 ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := B) 0).inv.app
          (F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus A 0).obj M)) ≫
        (DerivedCategory.Plus.homologyFunctor B 0).map
          (F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus A 0).obj M)) := by
  rw [rightDerivedSingleHomologyZeroIso_inv, NatTrans.comp_app]
  exact rightDerivedSingleHomologyIso_unit_zero F M

end CategoryTheory.Functor
