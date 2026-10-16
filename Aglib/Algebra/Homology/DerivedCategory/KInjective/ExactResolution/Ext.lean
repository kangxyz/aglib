/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.ExactResolution
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Native Ext classes of the exact-image resolution comparison

The original exact-functor map on Ext is computed by mapping the original
cocycle and following the actual comparison between the supplied
resolutions. Its augmentation certificate determines the comparison;
image terms need not be injective.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Localization
open CochainComplex HomComplex

namespace CategoryTheory.InjectiveResolution

universe u v u' v' w w' t

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{t} B]
  (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
  {M : A} (I : InjectiveResolution M) (J : InjectiveResolution (F.obj M))

local instance : PreservesFiniteLimits F :=
  Functor.preservesFiniteLimits_of_preservesHomology F

local instance : PreservesFiniteColimits F :=
  Functor.preservesFiniteColimits_of_preservesHomology F

local instance :
    (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)).functor.CommShift ℤ :=
  inferInstanceAs ((F.mapHomologicalComplex (.up ℤ)).CommShift ℤ)

/-- Map the original shifted chain cocycle and follow the actual resolution comparison.
The native single comparison retains the original source object. -/
def mapCochainComparisonCocycle {L : A} {n : ℤ}
    (c : Cocycle ((CochainComplex.singleFunctor A 0).obj L) I.cochainComplex n) :
    Cocycle ((CochainComplex.singleFunctor B 0).obj (F.obj L)) J.cochainComplex n :=
  Cocycle.equivHomShift
    ((ShiftedHom.mk₀ 0 rfl ((F.mapCochainComplexSingleFunctor 0).inv.app L)).comp
      ((ShiftedHom.map (Cocycle.equivHomShift.symm c) (F.mapHomologicalComplex (.up ℤ))).comp
        (ShiftedHom.mk₀ 0 rfl (mapCochainComparison F I J)) (zero_add n)) (add_zero n))

/-- In the native single coordinate, the mapped cocycle has the original mapped component
followed by the original resolution comparison component. -/
theorem mapCochainComparisonCocycle_fromSingleEquiv {L : A} {n : ℤ}
    (c : Cocycle ((CochainComplex.singleFunctor A 0).obj L) I.cochainComplex n) :
    Cochain.fromSingleEquiv (zero_add n) (mapCochainComparisonCocycle F I J c).1 =
      F.map (Cochain.fromSingleEquiv (zero_add n) c.1) ≫
        (mapCochainComparison F I J).f n := by
  simp only [Cochain.fromSingleEquiv, mapCochainComparisonCocycle, Functor.comp_obj,
    Functor.mapCochainComplexSingleFunctor, ShiftedHom.map, Cocycle.equivHomShift_symm_apply,
    ShiftedHom.comp_mk₀, Category.assoc, ShiftedHom.mk₀_comp, Cocycle.equivHomShift_apply,
    Cocycle.rightUnshift_coe, Cochain.rightUnshift, shiftFunctor_obj_X', Cocycle.ofHom_coe,
    Cochain.ofHom_comp, Cochain.comp_zero_cochain_v, Functor.mapHomologicalComplex_obj_X,
    Cochain.ofHom_v, Functor.mapHomologicalComplex_map_f, Cocycle.homOf_f,
    Cocycle.rightShift_coe, Cochain.rightShift, shiftFunctor_obj_X, shiftFunctorObjXIso,
    Cochain.mk_v, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Category.comp_id,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f, shiftFunctor_map_f', Category.id_comp,
    AddEquiv.coe_mk, Equiv.coe_fn_mk, Int.reduceAdd,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Iso.inv_hom_id_assoc,
    Functor.map_comp]
  let z := (c.1.map F).comp
    (Cochain.ofHom (mapCochainComparison F I J)) (add_zero n)
  have h := Cochain.v_comp_XIsoOfEq_hom z 0 (0 + n) n rfl (zero_add n)
  simp only [z, Cochain.comp_zero_cochain_v, Cochain.map_v, Cochain.ofHom_v] at h
  simpa only [Category.assoc] using congrArg
    (fun x => F.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).inv ≫ x) h

private theorem extEquivCohomologyClass_symm_mk_postcomp [HasExt.{w} A]
    {L : A} {n : ℕ}
    (c : Cocycle ((CochainComplex.singleFunctor A 0).obj L) I.cochainComplex n) :
    SmallShiftedHom.comp (I.extEquivCohomologyClass.symm (.mk c))
        (SmallShiftedHom.mk₀ (HomologicalComplex.quasiIso A (.up ℤ)) 0 rfl I.ι')
        (zero_add (n : ℤ)) =
      SmallShiftedHom.mk (HomologicalComplex.quasiIso A (.up ℤ))
        (Cocycle.equivHomShift.symm c) := by
  let e := SmallShiftedHom.postcompEquiv.{w}
    (W := HomologicalComplex.quasiIso A (.up ℤ)) (M := ℤ)
    (X := (CochainComplex.singleFunctor A 0).obj L) (a := (n : ℤ)) I.ι'
    (by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance)
  change e (e.symm ((CohomologyClass.equivOfIsKInjective) (.mk c))) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Original source precomposition on Ext is original single-complex precomposition on
the cocycle in any supplied injective resolution. -/
theorem extEquivCohomologyClass_symm_mk_precomp [HasExt.{w} A]
    {L L' : A} {n : ℕ}
    (c : Cocycle ((CochainComplex.singleFunctor A 0).obj L) I.cochainComplex n)
    (a : L' ⟶ L) :
    (Ext.mk₀ a).comp (I.extEquivCohomologyClass.symm (.mk c)) (Nat.zero_add n) =
      I.extEquivCohomologyClass.symm
        (.mk (c.precomp ((CochainComplex.singleFunctor A 0).map a))) := by
  let := HasDerivedCategory.standard A
  apply Ext.ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, extEquivCohomologyClass_symm_mk_hom,
    Cocycle.equivHomShift_symm_precomp]
  rw [← ShiftedHom.mk₀_comp 0 rfl, ShiftedHom.map_comp,
    ShiftedHom.comp_assoc _ _ _ (add_zero _) (zero_add _) (by simp),
    ← ShiftedHom.comp_assoc _ _ _ (add_zero _) (add_zero (n : ℤ)) (by simp)]
  simp

/-- The original exact-functor map on Ext is represented by the original mapped cocycle
followed by the actual resolution comparison. No image resolution term is assumed injective. -/
theorem mapCochainComparisonCocycle_extClass [HasExt.{w} A] [HasExt.{w'} B]
    {L : A} {n : ℕ}
    (c : Cocycle ((CochainComplex.singleFunctor A 0).obj L) I.cochainComplex n) :
    (I.extEquivCohomologyClass.symm (.mk c)).mapExactFunctor F =
      J.extEquivCohomologyClass.symm (.mk (mapCochainComparisonCocycle F I J c)) := by
  let K : CochainComplex B ℤ := (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let : K.IsGE 0 := by
    simp only [K, ← HomologicalComplex.isSupported_iff_of_quasiIso
      (mapCochainAugmentation F I)]
    infer_instance
  let : K.IsLE 0 := by
    simp only [K, ← HomologicalComplex.isSupported_iff_of_quasiIso
      (mapCochainAugmentation F I)]
    infer_instance
  let W₁ := HomologicalComplex.quasiIso A (.up ℤ)
  let W₂ := HomologicalComplex.quasiIso B (.up ℤ)
  let Φ := F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)
  let : HasSmallLocalizedShiftedHom.{w'} W₂ ℤ
      ((CochainComplex.singleFunctor B 0).obj (F.obj L)) K :=
    HasExt.hasSmallLocalizedShiftedHom_of_isLE_of_isGE _ _ 0 0
  let : HasSmallLocalizedShiftedHom.{w'} W₂ ℤ
      ((CochainComplex.singleFunctor B 0).obj (F.obj M)) K :=
    HasExt.hasSmallLocalizedShiftedHom_of_isLE_of_isGE _ _ 0 0
  let : HasSmallLocalizedShiftedHom.{w'} W₂ ℤ K K :=
    HasExt.hasSmallLocalizedShiftedHom_of_isLE_of_isGE _ _ 0 0
  let eL : (F.mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor A 0).obj L) ≅
      (CochainComplex.singleFunctor B 0).obj (F.obj L) :=
    (F.mapCochainComplexSingleFunctor 0).app L
  let eM : (F.mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor A 0).obj M) ≅
      (CochainComplex.singleFunctor B 0).obj (F.obj M) :=
    (F.mapCochainComplexSingleFunctor 0).app M
  let z := (ShiftedHom.mk₀ 0 rfl eL.inv).comp
    (ShiftedHom.map (Cocycle.equivHomShift.symm c) (F.mapHomologicalComplex (.up ℤ)))
    (add_zero (n : ℤ))
  have hf := Φ.smallShiftedHomMap_comp eL eM (Iso.refl K)
    (I.extEquivCohomologyClass.symm (.mk c))
    (SmallShiftedHom.mk₀ W₁ 0 rfl I.ι') (zero_add (n : ℤ))
  rw [extEquivCohomologyClass_symm_mk_postcomp] at hf
  rw [Φ.smallShiftedHomMap_mk, Φ.smallShiftedHomMap_mk₀] at hf
  simp only [Iso.refl_hom] at hf
  change SmallShiftedHom.mk W₂
      ((ShiftedHom.mk₀ 0 rfl eL.inv).comp
        ((ShiftedHom.map (Cocycle.equivHomShift.symm c)
          (F.mapHomologicalComplex (.up ℤ))).comp
            (ShiftedHom.mk₀ 0 rfl (𝟙 K)) (zero_add (n : ℤ))) (add_zero (n : ℤ))) =
    SmallShiftedHom.comp ((I.extEquivCohomologyClass.symm (.mk c)).mapExactFunctor F)
      (SmallShiftedHom.mk₀ W₂ 0 rfl
        (eM.inv ≫ (F.mapHomologicalComplex (.up ℤ)).map I.ι' ≫ 𝟙 K))
      (zero_add (n : ℤ)) at hf
  erw [Category.comp_id, ShiftedHom.comp_mk₀_id] at hf
  change SmallShiftedHom.mk W₂ z =
    SmallShiftedHom.comp ((I.extEquivCohomologyClass.symm (.mk c)).mapExactFunctor F)
      (SmallShiftedHom.mk₀ W₂ 0 rfl (mapCochainAugmentation F I)) (zero_add (n : ℤ)) at hf
  have hm := congrArg (SmallShiftedHom.equiv W₂ (DerivedCategory.Q (C := B))) hf.symm
  simp only [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk,
    SmallShiftedHom.equiv_mk₀] at hm
  have ha : (DerivedCategory.Q (C := B)).map (mapCochainAugmentation F I) ≫
      (DerivedCategory.Q (C := B)).map (mapCochainComparison F I J) =
      (DerivedCategory.Q (C := B)).map J.ι' := by
    rw [← Functor.map_comp]
    exact mapCochainAugmentation_comparison_Q_map F I J
  have hc : Cocycle.equivHomShift.symm (mapCochainComparisonCocycle F I J c) =
      z.comp (ShiftedHom.mk₀ 0 rfl (mapCochainComparison F I J)) (zero_add (n : ℤ)) := by
    simp only [mapCochainComparisonCocycle, AddEquiv.symm_apply_apply]
    exact (ShiftedHom.comp_assoc _ _ _ (add_zero (n : ℤ)) (zero_add (n : ℤ))
      (by simp)).symm
  let eJ := SmallShiftedHom.postcompEquiv.{w'}
    (W := W₂) (M := ℤ) (X := (CochainComplex.singleFunctor B 0).obj (F.obj L))
    (a := (n : ℤ)) J.ι' (by
      change HomologicalComplex.quasiIso B (.up ℤ) J.ι'
      rw [HomologicalComplex.mem_quasiIso_iff]
      infer_instance)
  apply eJ.injective
  change SmallShiftedHom.comp _ (SmallShiftedHom.mk₀ W₂ 0 rfl J.ι') _ =
    SmallShiftedHom.comp _ (SmallShiftedHom.mk₀ W₂ 0 rfl J.ι') _
  rw [extEquivCohomologyClass_symm_mk_postcomp]
  apply (SmallShiftedHom.equiv W₂ (DerivedCategory.Q (C := B))).injective
  dsimp only [W₂] at hm ⊢
  simp only [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀,
    SmallShiftedHom.equiv_mk]
  rw [hc, ShiftedHom.map_comp, ShiftedHom.map_mk₀, ← hm,
    ShiftedHom.comp_assoc _ _ _ (zero_add (n : ℤ)) (zero_add (0 : ℤ)) (by simp),
    ShiftedHom.mk₀_comp_mk₀, ha]

end CategoryTheory.InjectiveResolution
