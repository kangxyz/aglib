/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.ExtRightDerived
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Ext
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ZeroComparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition.Shift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Covariant connecting for the original Ext and right-derived Hom comparison

The original resolution cocycle identifies the Ext comparison with the action
of its shifted morphism after the native derived single unit. The unsigned
Ext boundary is then the third triangle arrow.

The resolution computations generalize the degree-one argument in
`Cohomology/DirectImage/ResolutionSections/Derived/Connecting.lean`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open CochainComplex HomComplex Opposite

universe u v e z u' v' z'

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{z} C]

private theorem plusQ_shifted_full
    {K L : CochainComplex.Plus C} {q : ℤ} (t : ShiftedHom K L q) :
    (t.map DerivedCategory.Plus.Q).map DerivedCategory.Plus.ι =
      (t.map (CochainComplex.Plus.ι C)).map DerivedCategory.Q := by
  let f : ShiftedHom (DerivedCategory.Q.obj K.obj) (DerivedCategory.Q.obj L.obj) q :=
    (t.map DerivedCategory.Plus.Q).map DerivedCategory.Plus.ι
  let g : ShiftedHom (DerivedCategory.Q.obj K.obj) (DerivedCategory.Q.obj L.obj) q :=
    (t.map (CochainComplex.Plus.ι C)).map DerivedCategory.Q
  have h := ShiftedHom.map_naturality t (DerivedCategory.Plus.QCompιIso C).hom
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_map,
    DerivedCategory.Plus.QCompιIso_hom_app] at h
  change f ≫ (𝟙 (DerivedCategory.Q.obj L.obj))⟦q⟧' =
    𝟙 (DerivedCategory.Q.obj K.obj) ≫ g at h
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] using h

private def resolutionCocyclePlus {M N : C} (I : InjectiveResolution N) {q : ℤ}
    (c : Cocycle ((CochainComplex.singleFunctor C 0).obj M) I.cochainComplex q) :
    ShiftedHom ((CochainComplex.singleFunctorPlus C 0).obj M)
      I.cochainComplexPlus q := by
  let K := (CochainComplex.singleFunctorPlus C 0).obj M
  let L := I.cochainComplexPlus
  let f : K.obj ⟶ L.obj⟦q⟧ := Cocycle.equivHomShift.symm c
  exact ObjectProperty.homMk
    (f ≫ ((CochainComplex.Plus.ι C).commShiftIso q).inv.app L)

omit [HasDerivedCategory C] in
private theorem resolutionCocyclePlus_full {M N : C} (I : InjectiveResolution N) {q : ℤ}
    (c : Cocycle ((CochainComplex.singleFunctor C 0).obj M) I.cochainComplex q) :
    (resolutionCocyclePlus I c).map (CochainComplex.Plus.ι C) =
      Cocycle.equivHomShift.symm c := by
  let K := (CochainComplex.singleFunctorPlus C 0).obj M
  let L := I.cochainComplexPlus
  let f : K.obj ⟶ L.obj⟦q⟧ := Cocycle.equivHomShift.symm c
  let e : ((CategoryTheory.shiftFunctor (CochainComplex.Plus C) q).obj L).obj ≅
      L.obj⟦q⟧ := ((CochainComplex.Plus.ι C).commShiftIso q).app L
  change (f ≫ e.inv) ≫ e.hom = f
  exact (Category.assoc f e.inv e.hom).trans
    ((congrArg (fun k => f ≫ k) e.inv_hom_id).trans (Category.comp_id f))

private theorem resolutionCocyclePlus_Q_full {M N : C} (I : InjectiveResolution N) {q : ℤ}
    (c : Cocycle ((CochainComplex.singleFunctor C 0).obj M) I.cochainComplex q) :
    ((resolutionCocyclePlus I c).map DerivedCategory.Plus.Q).map DerivedCategory.Plus.ι =
      ShiftedHom.map (Cocycle.equivHomShift.symm c) DerivedCategory.Q := by
  calc
    _ = ((resolutionCocyclePlus I c).map (CochainComplex.Plus.ι C)).map
        DerivedCategory.Q := plusQ_shifted_full (resolutionCocyclePlus I c)
    _ = _ := congrArg (fun f => ShiftedHom.map f DerivedCategory.Q)
      (resolutionCocyclePlus_full I c)

private theorem plusShiftedHom_map_injective
    {K L : DerivedCategory.Plus C} {q : ℤ}
    {f g : ShiftedHom K L q}
    (h : f.map DerivedCategory.Plus.ι = g.map DerivedCategory.Plus.ι) : f = g := by
  apply DerivedCategory.Plus.ι.map_injective
  exact (cancel_mono ((DerivedCategory.Plus.ι.commShiftIso q).hom.app L)).mp h

private theorem resolutionCocycle_ext_homPlus [HasExt.{e} C]
    {M N : C} (I : InjectiveResolution N) (n : ℕ)
    (c : Cocycle ((CochainComplex.singleFunctor C 0).obj M) I.cochainComplex (n : ℤ)) :
    (I.extEquivCohomologyClass.symm (.mk c) : Ext.{e} M N n).homPlus =
      ((resolutionCocyclePlus I c).map DerivedCategory.Plus.Q).comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl (inv (DerivedCategory.Plus.Q.map I.ιPlus)))
        (zero_add (n : ℤ)) := by
  apply plusShiftedHom_map_injective
  erw [Ext.homPlus_map, ShiftedHom.map_comp, ShiftedHom.map_mk₀,
    resolutionCocyclePlus_Q_full]
  let r : DerivedCategory.Q.obj I.cochainComplex ⟶
      (DerivedCategory.singleFunctor C 0).obj N :=
    DerivedCategory.Plus.ι.map (inv (DerivedCategory.Plus.Q.map I.ιPlus))
  change (I.extEquivCohomologyClass.symm (.mk c) : Ext.{e} M N n).hom =
    (ShiftedHom.map (Cocycle.equivHomShift.symm c) DerivedCategory.Q).comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl r) (zero_add (n : ℤ))
  have hr : r = inv (DerivedCategory.Q.map I.ι') := by
    dsimp only [r]
    erw [Functor.map_inv]; rfl
  rw [hr]
  rw [I.extEquivCohomologyClass_symm_mk_hom]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, ShiftedHom.mk₀_id_comp]
  let j : DerivedCategory.Q.obj I.cochainComplex ⟶
      (DerivedCategory.singleFunctor C 0).obj N := inv (DerivedCategory.Q.map I.ι')
  change (ShiftedHom.map (Cocycle.equivHomShift.symm c) DerivedCategory.Q).comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl
        (j ≫ 𝟙 ((DerivedCategory.singleFunctor C 0).obj N))) (zero_add (n : ℤ)) =
    (ShiftedHom.map (Cocycle.equivHomShift.symm c) DerivedCategory.Q).comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl j) (zero_add (n : ℤ))
  rw [Category.comp_id]

section Target
variable {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{z'} B]

private theorem plus_homology_shiftMap_full
    {K L : DerivedCategory.Plus B} {q : ℤ} (t : ShiftedHom K L q) :
    (DerivedCategory.Plus.homologyFunctor B 0).shiftMap
        t (0 : ℤ) q (by omega) =
      (DerivedCategory.homologyFunctor B 0).shiftMap
        (t.map DerivedCategory.Plus.ι) (0 : ℤ) q (by omega) := by
  let H := DerivedCategory.homologyFunctor B 0
  let ι : DerivedCategory.Plus B ⥤ DerivedCategory B :=
    DerivedCategory.Plus.ι
  let c : (L⟦q⟧).obj ⟶ L.obj⟦q⟧ := (ι.commShiftIso q).hom.app L
  let e : H.obj (L.obj⟦q⟧) ≅
      (DerivedCategory.homologyFunctor B q).obj L.obj :=
    (H.shiftIso q (0 : ℤ) q (by omega)).app L.obj
  change H.map t.hom ≫ (𝟙 _ ≫ H.map c ≫ 𝟙 _ ≫ e.hom) =
    H.map (t.hom ≫ c) ≫ e.hom
  simp only [Category.id_comp, Functor.map_comp, Category.assoc]

private theorem plus_homologyFactors_hom (K : CochainComplex.Plus B) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctorFactors (A := B) n).hom.app K =
      (DerivedCategory.homologyFunctorFactors B n).hom.app K.obj := by
  let Z : CochainComplex B ℤ := K.obj
  let W := DerivedCategory.Q.obj Z
  let H := DerivedCategory.homologyFunctor B n
  let h : H.obj W ⟶ Z.homology n :=
    (DerivedCategory.homologyFunctorFactors B n).hom.app Z
  let P : H.obj W ≅ Z.homology n :=
    (DerivedCategory.Plus.homologyFunctorFactors (A := B) n).app K
  have hp : P.hom = 𝟙 (H.obj W) ≫ H.map (𝟙 W) ≫ 𝟙 (H.obj W) ≫ h := rfl
  change P.hom = h
  exact hp.trans (by simp only [CategoryTheory.Functor.map_id, Category.id_comp])

private theorem plus_homologyFactors_inv (K : CochainComplex.Plus B) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctorFactors (A := B) n).inv.app K =
      (DerivedCategory.homologyFunctorFactors B n).inv.app K.obj := by
  let Z : CochainComplex B ℤ := K.obj
  let H := DerivedCategory.homologyFunctor B n
  let P : H.obj (DerivedCategory.Q.obj Z) ≅ Z.homology n :=
    (DerivedCategory.Plus.homologyFunctorFactors (A := B) n).app K
  let E : H.obj (DerivedCategory.Q.obj Z) ≅ Z.homology n :=
    (DerivedCategory.homologyFunctorFactors B n).app Z
  have h : P.hom = E.hom := plus_homologyFactors_hom K n
  change P.inv = E.inv
  exact congrArg (fun e : H.obj (DerivedCategory.Q.obj Z) ≅ Z.homology n => e.inv) (Iso.ext h)

private theorem plus_homology_shiftMap_Q
    {K L : CochainComplex.Plus B} {q : ℤ} (t : ShiftedHom K L q) :
    (DerivedCategory.Plus.homologyFunctor B 0).shiftMap
        (t.map DerivedCategory.Plus.Q) (0 : ℤ) q (by omega) =
      (DerivedCategory.Plus.homologyFunctorFactors (A := B) 0).hom.app K ≫
        (HomologicalComplex.homologyFunctor B (.up ℤ) 0).shiftMap
          (t.map (CochainComplex.Plus.ι B)) (0 : ℤ) q (by omega) ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := B) q).inv.app L := by
  rw [plus_homology_shiftMap_full, plusQ_shifted_full,
    plus_homologyFactors_hom, plus_homologyFactors_inv]
  change (DerivedCategory.homologyFunctor B 0).shiftMap
      ((t.map (CochainComplex.Plus.ι B)).map DerivedCategory.Q)
      (0 : ℤ) q (by omega) =
    (DerivedCategory.homologyFunctorFactors B 0).hom.app K.obj ≫
      (HomologicalComplex.homologyFunctor B (.up ℤ) 0).shiftMap
        (t.map (CochainComplex.Plus.ι B)) (0 : ℤ) q (by omega) ≫
      (DerivedCategory.homologyFunctorFactors B q).inv.app L.obj
  exact DerivedCategory.shiftMap_homologyFunctor_map_Q
    (t.map (CochainComplex.Plus.ι B)) (0 : ℤ) q (by omega)

private theorem single_homology_comparison (V : B) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).hom.app V =
      (DerivedCategory.Plus.homologyFunctorFactors (A := B) 0).hom.app
          ((CochainComplex.singleFunctorPlus B 0).obj V) ≫
        (singleObjHomologySelfIso (.up ℤ) 0 V).hom := by
  dsimp [DerivedCategory.singleFunctorCompHomologyFunctorIso,
    DerivedCategory.Plus.homologyFunctorFactors,
    DerivedCategory.singleFunctorsPostcompQIso, DerivedCategory.Plus.QCompιIso,
    ObjectProperty.liftCompιIso]
  let Z := (single B (.up ℤ) 0).obj V
  let W := DerivedCategory.Q.obj Z
  let H := DerivedCategory.homologyFunctor B 0
  let h : H.obj W ⟶ Z.homology 0 :=
    (DerivedCategory.homologyFunctorFactors B 0).hom.app Z
  let e : Z.homology 0 ⟶ V := (singleObjHomologySelfIso (.up ℤ) 0 V).hom
  change H.map (𝟙 W) ≫ 𝟙 (H.obj W) ≫ h ≫ e =
    (𝟙 (H.obj W) ≫ H.map (𝟙 W) ≫ 𝟙 (H.obj W) ≫ h) ≫ e
  simp only [Category.id_comp]
  exact (Category.assoc (H.map (𝟙 W)) h e).symm

private theorem single_to_Q_homology (V : B)
    (K : CochainComplex.Plus B)
    (τ : (CochainComplex.singleFunctorPlus B 0).obj V ⟶ K) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app V ≫
        (DerivedCategory.Plus.homologyFunctor B 0).map
          (DerivedCategory.Plus.Q.map τ) ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := B) 0).hom.app K =
      (singleObjHomologySelfIso (.up ℤ) 0 V).inv ≫ homologyMap τ.hom 0 := by
  let S := (CochainComplex.singleFunctorPlus B 0).obj V
  let P : (DerivedCategory.Plus.homologyFunctor B 0).obj
      (DerivedCategory.Plus.Q.obj S) ≅
      ((single B (.up ℤ) 0).obj V).homology 0 :=
    (DerivedCategory.Plus.homologyFunctorFactors (A := B) 0).app S
  have hE : (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app V =
      (singleObjHomologySelfIso (.up ℤ) 0 V).inv ≫ P.inv := by
    let E : (DerivedCategory.Plus.homologyFunctor B 0).obj
        (DerivedCategory.Plus.Q.obj S) ≅ V :=
      (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).app V
    let e : ((single B (.up ℤ) 0).obj V).homology 0 ≅ V :=
      singleObjHomologySelfIso (.up ℤ) 0 V
    have h : E.hom = (P ≪≫ e).hom := single_homology_comparison V
    change E.inv = e.inv ≫ P.inv
    exact congrArg (fun i : (DerivedCategory.Plus.homologyFunctor B 0).obj
      (DerivedCategory.Plus.Q.obj S) ≅ V => i.inv) (Iso.ext h)
  have hP := (DerivedCategory.Plus.homologyFunctorFactors
    (A := B) 0).hom.naturality τ
  change (DerivedCategory.Plus.homologyFunctor B 0).map
      (DerivedCategory.Plus.Q.map τ) ≫
      (DerivedCategory.Plus.homologyFunctorFactors (A := B) 0).hom.app K =
    P.hom ≫ homologyMap τ.hom 0 at hP
  erw [hE, Category.assoc, hP, Iso.inv_hom_id_assoc]

omit [HasDerivedCategory B] in
private theorem single_shifted_homology_from_component (q : ℤ)
    (V : B) (K : CochainComplex B ℤ)
    (t : (CochainComplex.singleFunctor B 0).obj V ⟶ K⟦q⟧)
    (f : V ⟶ K.X q) (hf : f ≫ K.d q (q + 1) = 0)
    (hcomp : (singleObjXSelf (.up ℤ) 0 V).inv ≫ t.f 0 ≫
        (K.shiftFunctorObjXIso q (0 : ℤ) q (by omega)).hom = f) :
    (singleObjHomologySelfIso (.up ℤ) 0 V).inv ≫
        (HomologicalComplex.homologyFunctor B (.up ℤ) 0).shiftMap
          t (0 : ℤ) q (by omega) =
      K.liftCycles f (q + 1) (by simp) hf ≫ K.homologyπ q := by
  let Z := K⟦q⟧
  let f₀ : V ⟶ Z.X 0 := (singleObjXSelf (.up ℤ) 0 V).inv ≫ t.f 0
  have hf₀ : f₀ ≫ Z.d 0 1 = 0 := by
    dsimp only [f₀]
    rw [Category.assoc, t.comm 0 1]
    simp
  let z := Z.liftCycles f₀ 1 (by simp) hf₀
  have hz : (singleObjCyclesSelfIso (.up ℤ) 0 V).inv ≫ cyclesMap t 0 = z := by
    apply (cancel_mono (Z.iCycles 0)).mp
    calc
      _ = (singleObjCyclesSelfIso (.up ℤ) 0 V).inv ≫
          (cyclesMap t 0 ≫ Z.iCycles 0) := Category.assoc _ _ _
      _ = (singleObjCyclesSelfIso (.up ℤ) 0 V).inv ≫
          (((single B (.up ℤ) 0).obj V).iCycles 0 ≫ t.f 0) :=
        congrArg (fun k => (singleObjCyclesSelfIso (.up ℤ) 0 V).inv ≫ k) (cyclesMap_i t 0)
      _ = f₀ := singleObjCyclesSelfIso_inv_iCycles_assoc (.up ℤ) 0 V (t.f 0)
      _ = _ := (Z.liftCycles_i f₀ 1 (by simp) hf₀).symm
  have hh : (singleObjHomologySelfIso (.up ℤ) 0 V).inv ≫ homologyMap t 0 =
      z ≫ Z.homologyπ 0 := by
    rw [← singleObjCyclesSelfIso_inv_homologyπ]
    simp only [Category.assoc, homologyπ_naturality]
    rw [← Category.assoc, hz]
  let E : Z.homology 0 ≅ K.homology q :=
    ((HomologicalComplex.homologyFunctor B (.up ℤ) 0).shiftIso
      q (0 : ℤ) q (by omega)).app K
  let f' : V ⟶ K.X q := f₀ ≫
    (K.shiftFunctorObjXIso q (0 : ℤ) q (by omega)).hom
  have hff : f' = f := by simpa only [f', f₀, Category.assoc] using hcomp
  have hf' : f' ≫ K.d q (q + 1) = 0 := (congrArg (fun k => k ≫ K.d q (q + 1)) hff).trans hf
  have hshift : z ≫ Z.homologyπ 0 =
      K.liftCycles f' (q + 1) (by simp) hf' ≫ K.homologyπ q ≫ E.inv :=
    CochainComplex.liftCycles_shift_homologyπ K f₀ 1 (by simp) hf₀
      q (by omega) (q + 1) (by simp)
  rw [Functor.shiftMap, ← Category.assoc]
  change ((singleObjHomologySelfIso (.up ℤ) 0 V).inv ≫ homologyMap t 0) ≫ E.hom = _
  calc
    _ = (z ≫ Z.homologyπ 0) ≫ E.hom := congrArg (fun k => k ≫ E.hom) hh
    _ = (K.liftCycles f' (q + 1) (by simp) hf' ≫ K.homologyπ q ≫ E.inv) ≫ E.hom :=
      congrArg (fun k => k ≫ E.hom) hshift
    _ = K.liftCycles f' (q + 1) (by simp) hf' ≫ K.homologyπ q := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := by
      congr 1
      apply (cancel_mono (K.iCycles q)).mp
      exact (K.liftCycles_i f' (q + 1) (by simp) hf').trans
        (hff.trans (K.liftCycles_i f (q + 1) (by simp) hf).symm)

end Target

variable [EnoughInjectives C]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{z'} B]
  (F : C ⥤ B) [F.Additive]

private def mappedResolutionCocycle {M N : C} (I : InjectiveResolution N) (n : ℕ)
    (c : Cocycle ((CochainComplex.singleFunctor C 0).obj M) I.cochainComplex (n : ℤ)) :
    ShiftedHom ((DerivedCategory.Plus.singleFunctor B 0).obj
      (F.obj M))
      (DerivedCategory.Plus.Q.obj
        (F.mapCochainComplexPlus.obj
          I.cochainComplexPlus)) (n : ℤ) :=
  DerivedCategory.Plus.Q.map
      (show (CochainComplex.singleFunctorPlus B 0).obj
          (F.obj M) ⟶
        F.mapCochainComplexPlus.obj
          ((CochainComplex.singleFunctorPlus C 0).obj M) from
        ObjectProperty.homMk ((singleMapHomologicalComplex
          F (.up ℤ) 0).inv.app M)) ≫
    ((resolutionCocyclePlus I c).map
      F.mapCochainComplexPlus).map DerivedCategory.Plus.Q

private theorem derivedUnit_resolutionCocycle [HasExt.{e} C]
    {M N : C} (I : InjectiveResolution N) (n : ℕ)
    (c : Cocycle ((CochainComplex.singleFunctor C 0).obj M) I.cochainComplex (n : ℤ)) :
    F.rightDerivedSingleUnit M ≫
        ((I.extEquivCohomologyClass.symm (.mk c) : Ext.{e} M N n).homPlus.map
          F.rightDerivedFunctorPlus) =
      mappedResolutionCocycle F I n c ≫
        (I.rightDerivedFunctorPlusIso F).hom⟦(n : ℤ)⟧' := by
  let t := resolutionCocyclePlus I c
  let a := (I.extEquivCohomologyClass.symm (.mk c) : Ext.{e} M N n).homPlus
  let p : DerivedCategory.Plus.Q.obj ((CochainComplex.singleFunctorPlus C 0).obj N) ⟶
      DerivedCategory.Plus.Q.obj I.cochainComplexPlus := DerivedCategory.Plus.Q.map I.ιPlus
  let q : ShiftedHom
      (DerivedCategory.Plus.Q.obj ((CochainComplex.singleFunctorPlus C 0).obj M))
      (DerivedCategory.Plus.Q.obj I.cochainComplexPlus) (n : ℤ) := t.map DerivedCategory.Plus.Q
  let σ : (CochainComplex.singleFunctorPlus B 0).obj (F.obj M) ⟶
      F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus C 0).obj M) :=
    ObjectProperty.homMk ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)
  have hq : mappedResolutionCocycle F I n c = DerivedCategory.Plus.Q.map σ ≫
      (t.map F.mapCochainComplexPlus).map DerivedCategory.Plus.Q := rfl
  have ha : a.comp (ShiftedHom.mk₀ (0 : ℤ) rfl p) (zero_add (n : ℤ)) =
      t.map DerivedCategory.Plus.Q := by
    dsimp only [a, t, p]
    erw [resolutionCocycle_ext_homPlus, ShiftedHom.comp_mk₀, ShiftedHom.comp_mk₀]
    change (q ≫ (inv p)⟦(n : ℤ)⟧') ≫ p⟦(n : ℤ)⟧' = q
    rw [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have haF : a.map F.rightDerivedFunctorPlus ≫
      (F.rightDerivedFunctorPlus.map p)⟦(n : ℤ)⟧' =
      (t.map DerivedCategory.Plus.Q).map F.rightDerivedFunctorPlus := by
    have h := congrArg (fun f => f.map F.rightDerivedFunctorPlus) ha
    erw [ShiftedHom.map_comp, ShiftedHom.map_mk₀, ShiftedHom.comp_mk₀] at h
    exact h
  have hη := ShiftedHom.map_naturality t F.rightDerivedFunctorPlusUnit
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_map] at hη
  apply (cancel_mono ((F.rightDerivedFunctorPlus.map p)⟦(n : ℤ)⟧')).mp
  change (F.rightDerivedSingleUnit M ≫ a.map F.rightDerivedFunctorPlus) ≫
      (F.rightDerivedFunctorPlus.map p)⟦(n : ℤ)⟧' =
    (mappedResolutionCocycle F I n c ≫ (I.rightDerivedFunctorPlusIso F).hom⟦(n : ℤ)⟧') ≫
      (F.rightDerivedFunctorPlus.map p)⟦(n : ℤ)⟧'
  rw [Category.assoc, haF]
  change (DerivedCategory.Plus.Q.map σ ≫
      F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus C 0).obj M)) ≫
        (t.map DerivedCategory.Plus.Q).map F.rightDerivedFunctorPlus = _
  rw [Category.assoc, ← hη]
  have he : (I.rightDerivedFunctorPlusIso F).hom⟦(n : ℤ)⟧' ≫
      (F.rightDerivedFunctorPlus.map p)⟦(n : ℤ)⟧' =
      (F.rightDerivedFunctorPlusUnit.app I.cochainComplexPlus)⟦(n : ℤ)⟧' := by
    let Sh := CategoryTheory.shiftFunctor (DerivedCategory.Plus B) (n : ℤ)
    have h := congrArg Sh.map (I.rightDerivedFunctorPlusIso_hom_comp F)
    simpa only [Functor.map_comp] using h
  have hrhs : (mappedResolutionCocycle F I n c ≫
      (I.rightDerivedFunctorPlusIso F).hom⟦(n : ℤ)⟧') ≫
      (F.rightDerivedFunctorPlus.map p)⟦(n : ℤ)⟧' =
      mappedResolutionCocycle F I n c ≫
        (F.rightDerivedFunctorPlusUnit.app I.cochainComplexPlus)⟦(n : ℤ)⟧' := by
    rw [Category.assoc, he]
  let U := (DerivedCategory.Plus.singleFunctor B 0).obj (F.obj M)
  let V := DerivedCategory.Plus.Q.obj
    (F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus C 0).obj M))
  let J := DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj I.cochainComplexPlus)
  let W := F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj I.cochainComplexPlus)
  let s : U ⟶ V := DerivedCategory.Plus.Q.map σ
  let v : ShiftedHom V J (n : ℤ) :=
    (t.map F.mapCochainComplexPlus).map DerivedCategory.Plus.Q
  let k : ShiftedHom U J (n : ℤ) := mappedResolutionCocycle F I n c
  let h : J ⟶ W := F.rightDerivedFunctorPlusUnit.app I.cochainComplexPlus
  have hk : k = s ≫ v := hq
  have hl : s ≫ v ≫ h⟦(n : ℤ)⟧' = k ≫ h⟦(n : ℤ)⟧' :=
    (Category.assoc s v (h⟦(n : ℤ)⟧')).symm.trans
      (congrArg (fun q : ShiftedHom U J (n : ℤ) => q ≫ h⟦(n : ℤ)⟧') hk.symm)
  have hr : (k ≫ (I.rightDerivedFunctorPlusIso F).hom⟦(n : ℤ)⟧') ≫
      (F.rightDerivedFunctorPlus.map p)⟦(n : ℤ)⟧' = k ≫ h⟦(n : ℤ)⟧' := hrhs
  change s ≫ v ≫ h⟦(n : ℤ)⟧' =
    (k ≫ (I.rightDerivedFunctorPlusIso F).hom⟦(n : ℤ)⟧') ≫
      (F.rightDerivedFunctorPlus.map p)⟦(n : ℤ)⟧'
  exact hl.trans hr.symm

omit [HasDerivedCategory C] [EnoughInjectives C] [HasDerivedCategory B] in
private theorem resolutionCocyclePlus_map_full {M N : C} (I : InjectiveResolution N) (n : ℕ)
    (c : Cocycle ((CochainComplex.singleFunctor C 0).obj M) I.cochainComplex (n : ℤ)) :
    ((resolutionCocyclePlus I c).map
        F.mapCochainComplexPlus).map
          (CochainComplex.Plus.ι B) =
      ShiftedHom.map (Cocycle.equivHomShift.symm c)
        (F.mapHomologicalComplex (.up ℤ)) := by
  let K : CochainComplex C ℤ := (CochainComplex.singleFunctor C 0).obj M
  let L : CochainComplex C ℤ := I.cochainComplex
  let f : ShiftedHom ((F.mapHomologicalComplex (.up ℤ)).obj K)
      ((F.mapHomologicalComplex (.up ℤ)).obj L) (n : ℤ) :=
    ((resolutionCocyclePlus I c).map F.mapCochainComplexPlus).map
      (CochainComplex.Plus.ι B)
  let g : ShiftedHom ((F.mapHomologicalComplex (.up ℤ)).obj K)
      ((F.mapHomologicalComplex (.up ℤ)).obj L) (n : ℤ) :=
    ShiftedHom.map (Cocycle.equivHomShift.symm c) (F.mapHomologicalComplex (.up ℤ))
  have h := ShiftedHom.map_naturality (resolutionCocyclePlus I c)
    F.mapCochainComplexPlusCompι.hom
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_map,
    Functor.mapCochainComplexPlusCompι_hom_app, resolutionCocyclePlus_full] at h
  change f ≫ (𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj L))⟦(n : ℤ)⟧' =
    𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫ g at h
  change f = g
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] using h

omit [HasDerivedCategory C] [EnoughInjectives C] in
private theorem fromSingleCocycle_component {M N : C} (I : InjectiveResolution N) (n : ℕ)
    (f : M ⟶ I.cochainComplex.X (n : ℤ)) (hf : f ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0) :
    (singleObjXSelf (.up ℤ) 0 M).inv ≫
        (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk f (zero_add (n : ℤ)) ((n : ℤ) + 1) rfl hf)).f 0 ≫
        (I.cochainComplex.shiftFunctorObjXIso (n : ℤ) (0 : ℤ) (n : ℤ) (by omega)).hom = f := by
  simp only [Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f, Cocycle.rightShift_coe]
  rw [Cochain.rightShift_v _ (n : ℤ) 0 (zero_add (n : ℤ)) 0 0 (add_zero 0) (n : ℤ) (zero_add _)]
  simp only [Cocycle.fromSingleMk_coe, Cochain.fromSingleMk_v,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

omit [HasDerivedCategory C] [EnoughInjectives C] [HasDerivedCategory B] in
private theorem sectionComplex_cycle_condition {M N : C} (I : InjectiveResolution N) (n : ℕ)
    (f : M ⟶ I.cochainComplex.X (n : ℤ)) (hf : f ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0) :
    F.map f ≫
      ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).d (n : ℤ) ((n : ℤ) + 1) = 0 := by
  change F.map f ≫ F.map (I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1)) = 0
  exact (F.map_comp f (I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1))).symm.trans
    ((congrArg F.map hf).trans (F.map_zero M (I.cochainComplex.X ((n : ℤ) + 1))))

omit [HasDerivedCategory C] [EnoughInjectives C] in
private theorem mappedResolutionCocycle_homology {M N : C} (I : InjectiveResolution N) (n : ℕ)
    (f : M ⟶ I.cochainComplex.X (n : ℤ)) (hf : f ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app
        (F.obj M) ≫
      (DerivedCategory.Plus.homologyFunctor B 0).shiftMap
        (mappedResolutionCocycle F I n
          (Cocycle.fromSingleMk f (zero_add (n : ℤ)) ((n : ℤ) + 1) rfl hf))
        (0 : ℤ) (n : ℤ) (by omega) ≫
      (DerivedCategory.Plus.homologyFunctorFactors (A := B) (n : ℤ)).hom.app
        (F.mapCochainComplexPlus.obj I.cochainComplexPlus) =
    ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).liftCycles
        (F.map f) ((n : ℤ) + 1) (by simp)
        (sectionComplex_cycle_condition F I n f hf) ≫
      ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homologyπ (n : ℤ) := by
  let c := Cocycle.fromSingleMk f (zero_add (n : ℤ)) ((n : ℤ) + 1) rfl hf
  let K := F.mapCochainComplexPlus.obj I.cochainComplexPlus
  let L := F.mapCochainComplexPlus.obj
    ((CochainComplex.singleFunctorPlus C 0).obj M)
  let τ : (CochainComplex.singleFunctorPlus B 0).obj (F.obj M) ⟶ L :=
    ObjectProperty.homMk ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)
  let t := (resolutionCocyclePlus I c).map F.mapCochainComplexPlus
  let Kfull : CochainComplex B ℤ := (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let Lfull : CochainComplex B ℤ :=
    (F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj M)
  let τfull : (CochainComplex.singleFunctor B 0).obj (F.obj M) ⟶ Lfull :=
    (singleMapHomologicalComplex F (.up ℤ) 0).inv.app M
  let tFull : ShiftedHom Lfull Kfull (n : ℤ) :=
    t.map (CochainComplex.Plus.ι B)
  have ht : tFull = ShiftedHom.map (Cocycle.equivHomShift.symm c)
      (F.mapHomologicalComplex (.up ℤ)) := resolutionCocyclePlus_map_full F I n c
  have hcomp : (singleObjXSelf (.up ℤ) 0 (F.obj M)).inv ≫ (τfull ≫ tFull).f 0 ≫
      (Kfull.shiftFunctorObjXIso (n : ℤ) (0 : ℤ) (n : ℤ) (by omega)).hom = F.map f := by
    rw [ht]
    change (singleObjXSelf (.up ℤ) 0 (F.obj M)).inv ≫
        ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M ≫
          ShiftedHom.map (Cocycle.equivHomShift.symm c)
            (F.mapHomologicalComplex (.up ℤ))).f 0 ≫
        (CochainComplex.shiftFunctorObjXIso
          ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)
          (n : ℤ) (0 : ℤ) (n : ℤ) (by omega)).hom = F.map f
    simp only [HomologicalComplex.comp_f, ShiftedHom.map,
      singleMapHomologicalComplex_inv_app_self, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Category.assoc, Iso.inv_hom_id_assoc]
    have hs (j : ℤ) (hj : j = 0 + (n : ℤ)) :
        (Kfull.shiftFunctorObjXIso (n : ℤ) 0 j hj).hom =
          F.map (I.cochainComplex.shiftFunctorObjXIso (n : ℤ) 0 j hj).hom := by
      subst j
      simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
        Iso.refl_hom]
      exact (F.map_id (I.cochainComplex.X (0 + (n : ℤ)))).symm
    rw [hs]
    let e : M ⟶ ((CochainComplex.singleFunctor C 0).obj M).X 0 :=
      (singleObjXSelf (.up ℤ) 0 M).inv
    let r : ((CochainComplex.singleFunctor C 0).obj M).X 0 ⟶
        (I.cochainComplex⟦(n : ℤ)⟧).X 0 := (Cocycle.equivHomShift.symm c).f 0
    let j := (I.cochainComplex.shiftFunctorObjXIso (n : ℤ) 0 (n : ℤ) (by omega)).hom
    change F.map e ≫ F.map r ≫ 𝟙 (F.obj ((I.cochainComplex⟦(n : ℤ)⟧).X 0)) ≫
      F.map j = F.map f
    rw [Category.id_comp, ← F.map_comp_assoc, ← F.map_comp]
    have hc : (e ≫ r) ≫ j = f :=
      (Category.assoc e r j).trans (fromSingleCocycle_component I n f hf)
    exact congrArg F.map hc
  let H := DerivedCategory.Plus.homologyFunctor B 0
  let Hc := HomologicalComplex.homologyFunctor B (.up ℤ) 0
  let P₀ : H.obj (DerivedCategory.Plus.Q.obj L) ≅ Lfull.homology 0 :=
    (DerivedCategory.Plus.homologyFunctorFactors (A := B) 0).app L
  let P₁ : (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).obj
      (DerivedCategory.Plus.Q.obj K) ≅ Kfull.homology (n : ℤ) :=
    (DerivedCategory.Plus.homologyFunctorFactors (A := B) (n : ℤ)).app K
  let e₀ : F.obj M ⟶
      ((CochainComplex.singleFunctor B 0).obj (F.obj M)).homology 0 :=
    (singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).inv
  let t₀ : Lfull.homology 0 ⟶ Kfull.homology (n : ℤ) :=
    Hc.shiftMap tFull (0 : ℤ) (n : ℤ) (by omega)
  let τt₀ : ((CochainComplex.singleFunctor B 0).obj (F.obj M)).homology 0 ⟶
      Kfull.homology (n : ℤ) := Hc.shiftMap (τfull ≫ tFull) (0 : ℤ) (n : ℤ) (by omega)
  let l : F.obj M ⟶ Kfull.cycles (n : ℤ) :=
    Kfull.liftCycles (F.map f) ((n : ℤ) + 1) (by simp) (sectionComplex_cycle_condition F I n f hf)
  let d₀ : F.obj M ⟶ H.obj (DerivedCategory.Plus.Q.obj
      ((CochainComplex.singleFunctorPlus B 0).obj (F.obj M))) :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app (F.obj M)
  have hsingle : d₀ ≫ H.map (DerivedCategory.Plus.Q.map τ) ≫ P₀.hom =
      e₀ ≫ homologyMap τfull 0 :=
    single_to_Q_homology (F.obj M) L τ
  have hshift : homologyMap τfull 0 ≫ t₀ = τt₀ :=
    (Hc.shiftMap_comp' τfull tFull (0 : ℤ) (n : ℤ) (by omega)).symm
  have hfinal : e₀ ≫ τt₀ = l ≫ Kfull.homologyπ (n : ℤ) :=
    single_shifted_homology_from_component (n : ℤ) (F.obj M) Kfull
      (τfull ≫ tFull) (F.map f) (sectionComplex_cycle_condition F I n f hf) hcomp
  change d₀ ≫
      H.shiftMap (DerivedCategory.Plus.Q.map τ ≫ t.map DerivedCategory.Plus.Q)
        (0 : ℤ) (n : ℤ) (by omega) ≫ P₁.hom = l ≫ Kfull.homologyπ (n : ℤ)
  calc
    _ = (d₀ ≫ H.map (DerivedCategory.Plus.Q.map τ) ≫ P₀.hom) ≫ t₀ := by
      rw [Functor.shiftMap_comp', plus_homology_shiftMap_Q]
      change d₀ ≫ ((H.map (DerivedCategory.Plus.Q.map τ) ≫
          P₀.hom ≫ t₀ ≫ P₁.inv) ≫ P₁.hom) =
        (d₀ ≫ H.map (DerivedCategory.Plus.Q.map τ) ≫ P₀.hom) ≫ t₀
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = (e₀ ≫ homologyMap τfull 0) ≫ t₀ :=
      congrArg (fun k : F.obj M ⟶ Lfull.homology 0 => k ≫ t₀) hsingle
    _ = e₀ ≫ τt₀ := (Category.assoc _ _ _).trans (congrArg (fun k => e₀ ≫ k) hshift)
    _ = _ := hfinal

/-- The original resolution cycle computes the shifted Ext action after the
native derived single unit, with the same target homology comparisons. -/
theorem derivedUnit_cocycle_homology [HasExt.{e} C]
    {M N : C} (I : InjectiveResolution N) (n : ℕ)
    (f : M ⟶ I.cochainComplex.X (n : ℤ))
    (hf : f ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0) :
    let H := DerivedCategory.Plus.homologyFunctor B 0
    let c := Cocycle.fromSingleMk f (zero_add (n : ℤ)) ((n : ℤ) + 1) rfl hf
    let a : Ext.{e} M N n := I.extEquivCohomologyClass.symm (.mk c)
    let K := ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app (F.obj M) ≫
      H.shiftMap (F.rightDerivedSingleUnit M ≫ a.homPlus.map F.rightDerivedFunctorPlus)
        0 (n : ℤ) (by omega) =
    K.liftCycles (F.map f) ((n : ℤ) + 1) (by simp)
      (by
        change F.map f ≫ F.map (I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1)) = 0
        rw [← F.map_comp, hf, F.map_zero]) ≫ K.homologyπ (n : ℤ) ≫
      (DerivedCategory.Plus.homologyFunctorFactors (A := B) (n : ℤ)).inv.app
        (F.mapCochainComplexPlus.obj I.cochainComplexPlus) ≫
      (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
        (I.rightDerivedFunctorPlusIso F).hom := by
  dsimp only
  rw [derivedUnit_resolutionCocycle, Functor.shiftMap_comp, ← Category.assoc]
  have h := mappedResolutionCocycle_homology F I n f hf
  let E := (DerivedCategory.Plus.homologyFunctorFactors (A := B) (n : ℤ)).app
    (F.mapCochainComplexPlus.obj I.cochainComplexPlus)
  have hc := (Iso.eq_comp_inv E).mpr ((Category.assoc _ _ _).trans h)
  exact (congrArg (fun k => k ≫
    (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
      (I.rightDerivedFunctorPlusIso F).hom) hc).trans
    (by simp only [Category.assoc, E, Iso.app_inv])

end CategoryTheory.InjectiveResolution

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{z} C]
  [EnoughInjectives C] [HasExt.{e} C] [HasDerivedCategory (AddCommGrpCat.{v})]

/-- Evaluating the actual shifted Ext map after the original derived single
unit gives the original cocycle-normalized Ext comparison. -/
theorem extRightDerivedAddEquiv_homPlus {P N : C} (I : InjectiveResolution N) (n : ℕ)
    (x : Ext.{e} P N n) :
    let F := preadditiveCoyoneda.obj (op P)
    (F.rightDerivedSingleHomologyIso n).hom.app N (I.extRightDerivedAddEquiv P n x) =
      (DerivedCategory.Plus.homologyFunctor (AddCommGrpCat.{v}) 0).shiftMap
        (F.rightDerivedSingleUnit P ≫ x.homPlus.map F.rightDerivedFunctorPlus)
        0 (n : ℤ) (by omega)
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (AddCommGrpCat.{v}) 0).inv.app
          (F.obj P) (𝟙 P)) := by
  let F := preadditiveCoyoneda.obj (op P)
  obtain ⟨a, rfl⟩ := I.extEquivCohomologyClass.symm.surjective x
  obtain ⟨c, rfl⟩ := a.mk_surjective
  obtain ⟨f, hf, rfl⟩ :=
    Cocycle.fromSingleMk_surjective c (n : ℤ) (zero_add (n : ℤ)) ((n : ℤ) + 1) rfl
  let K := (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let l := K.liftCycles (F.map f) ((n : ℤ) + 1) (by simp)
    (sectionComplex_cycle_condition F I n f hf)
  let y := (K.sc (n : ℤ)).abCyclesIso.inv ⟨f, by
    change f ≫ I.cochainComplex.d (n : ℤ) ((ComplexShape.up ℤ).next (n : ℤ)) = 0
    rw [CochainComplex.next]
    exact hf⟩
  have hy : l (𝟙 P) = y := by
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles (n : ℤ))).mp inferInstance
    rw [← ConcreteCategory.comp_apply, liftCycles_i]
    have h : K.iCycles (n : ℤ) y = f := by
      dsimp only [y]
      erw [HomologicalComplex.iCycles, ShortComplex.abCyclesIso_inv_apply_iCycles]
    rw [h]
    change 𝟙 P ≫ f = f
    exact Category.id_comp f
  dsimp only
  rw [I.extRightDerivedAddEquiv_cocycle, F.rightDerivedSingleHomologyIso_hom_app I,
    isoRightDerivedSingleHomology_hom]
  have h := ConcreteCategory.congr_hom (derivedUnit_cocycle_homology F I n f hf) (𝟙 P)
  simp only [ConcreteCategory.comp_apply] at h ⊢
  change (DerivedCategory.Plus.homologyFunctor (AddCommGrpCat.{v}) (n : ℤ)).map
      (I.rightDerivedFunctorPlusIso F).hom
      ((DerivedCategory.Plus.homologyFunctorFactors (A := AddCommGrpCat.{v}) (n : ℤ)).inv.app
        (F.mapCochainComplexPlus.obj I.cochainComplexPlus)
        ((I.isoRightDerivedObjCochain F n).hom
          ((I.isoRightDerivedObjCochain F n).inv (K.homologyπ (n : ℤ) y)))) = _
  rw [← hy]
  have hi := ConcreteCategory.congr_hom (I.isoRightDerivedObjCochain F n).inv_hom_id
    (K.homologyπ (n : ℤ) (l (𝟙 P)))
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hi
  rw [hi]
  exact h.symm

omit [HasDerivedCategory (AddCommGrpCat.{v})] in
private theorem shiftMap_shiftedComp
    {D E : Type*} [Category* D] [Category* E] [HasShift D ℤ]
    (F : D ⥤ E) [F.ShiftSequence ℤ] {U V W : D} {a b c : ℤ}
    (f : ShiftedHom U V a) (g : ShiftedHom V W b) (h : b + a = c) :
    F.shiftMap (f.comp g h) 0 c (add_zero _) =
      F.shiftMap f 0 a (add_zero _) ≫ F.shiftMap g a c h := by
  symm
  calc
    _ = (F.shift 0).map f ≫
        (F.shiftIso a 0 a (add_zero a)).hom.app V ≫ F.shiftMap g a c h := by
      simp only [Functor.shiftMap, Category.assoc]
    _ = _ := by
      rw [F.shiftIso_hom_app_comp_shiftMap g a c h 0 a c (add_zero a) h]
      simp only [ShiftedHom.comp, Functor.shiftMap, Functor.map_comp, Category.assoc]

/-- The original additive Hom comparison intertwines unsigned Ext
postcomposition with the actual boundary of the installed derived triangle. -/
theorem extRightDerivedAddEquiv_connecting {P : C} {S : ShortComplex C} (hS : S.ShortExact)
    (I₁ : InjectiveResolution S.X₁) (I₃ : InjectiveResolution S.X₃) (n : ℕ)
    (x : Ext.{e} P S.X₃ n) :
    let F := preadditiveCoyoneda.obj (op P)
    (F.rightDerivedSingleHomologyIso (n + 1)).hom.app S.X₁
        (I₁.extRightDerivedAddEquiv P (n + 1) (x.comp hS.extClass rfl)) =
      (DerivedCategory.Plus.homologyFunctor (AddCommGrpCat.{v}) 0).homologySequenceδ
        (F.rightDerivedFunctorPlus.mapTriangle.obj hS.singleTrianglePlus)
        (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)
        ((F.rightDerivedSingleHomologyIso n).hom.app S.X₃
          (I₃.extRightDerivedAddEquiv P n x)) := by
  let F := preadditiveCoyoneda.obj (op P)
  let H := DerivedCategory.Plus.homologyFunctor (AddCommGrpCat.{v}) 0
  dsimp only
  rw [I₁.extRightDerivedAddEquiv_homPlus, I₃.extRightDerivedAddEquiv_homPlus]
  have hc : (x.comp hS.extClass rfl).homPlus.map F.rightDerivedFunctorPlus =
      (x.homPlus.map F.rightDerivedFunctorPlus).comp
        (hS.extClass.homPlus.map F.rightDerivedFunctorPlus)
        (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega) := by
    rw [Ext.homPlus_comp, ShiftedHom.map_comp]
  rw [hc]
  have hδ : H.homologySequenceδ
      (F.rightDerivedFunctorPlus.mapTriangle.obj hS.singleTrianglePlus)
      (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega) =
    H.shiftMap (hS.extClass.homPlus.map F.rightDerivedFunctorPlus)
      (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega) := by
    rw [Ext.homPlus_extClass]
    rfl
  rw [hδ, H.shiftMap_comp', H.shiftMap_comp']
  rw [shiftMap_shiftedComp, ← Category.assoc]
  rfl

end CategoryTheory.InjectiveResolution
