/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Derived
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Exact
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Ext
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ZeroComparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition.Shift
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.ExactResolution.Ext
public import Aglib.CategoryTheory.Abelian.Injective.ExtZero
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Original section and connecting-map normalization of derived global sections

The original supplied-resolution comparison preserves the actual degree-zero
sections and the actual positive degree-zero to degree-one connecting map.
The proof retains the original augmentation, Ext cocycle and native shifts.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open CochainComplex HomComplex
open AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))

/-- The standard derived category of module sheaves for the source of global sections. -/
local instance connectingSource : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

/-- The standard derived category of `R`-modules for the target of global sections. -/
local instance connectingTarget : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

private theorem moduleH0EquivOfHom_extMk₀ (M : X.Modules)
    (g : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) :
    let := moduleCohomologyModuleOfHom X α M 0
    moduleH0EquivOfHom X α M (moduleExtCohomologyMap X M 0 (Ext.mk₀ g)) =
      Scheme.Modules.unitHomGlobalSectionsEquiv X M g := by
  let := moduleCohomologyModuleOfHom X α M 0
  let g' := moduleUnitIntegerMap X ≫ (SheafOfModules.toSheaf X.ringCatSheaf).map g
  have hg : Ext.addEquiv₀ (Ext.mk₀ g') = g' :=
    (Ext.mk₀_bijective _ _).injective (Ext.mk₀_addEquiv₀_apply _)
  rw [moduleExtCohomologyMap_mk₀]
  change integerSheafHomEquiv (moduleAddSheaf X M) (Ext.addEquiv₀ (Ext.mk₀ g')) = _
  rw [hg]
  change integerSheafHomEquiv (moduleAddSheaf X M)
    (moduleUnitIntegerMap X ≫ (SheafOfModules.toSheaf X.ringCatSheaf).map g) = _
  rw [integerSheafHomEquiv_comp, moduleUnitIntegerMap_sections]
  rfl

private theorem zeroComparison_inv_resolution (M : X.Modules) (I : InjectiveResolution M) :
    (moduleGlobalSectionsFunctorOfHom X α).rightDerivedSingleHomologyZeroIso.inv.app M =
      I.toRightDerivedZeroCochainCycles (moduleGlobalSectionsFunctorOfHom X α) ≫
        (moduleResolutionSectionComplex X α I).homologyπ 0 ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) 0).inv.app
          ((moduleGlobalSectionsFunctorOfHom X α).mapCochainComplexPlus.obj
            I.cochainComplexPlus) ≫
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
          (I.rightDerivedFunctorPlusIso (moduleGlobalSectionsFunctorOfHom X α)).hom := by
  let F := moduleGlobalSectionsFunctorOfHom X α
  let P := (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) 0).app
    (F.mapCochainComplexPlus.obj I.cochainComplexPlus)
  let e := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
    (I.rightDerivedFunctorPlusIso F).hom
  calc
    _ = F.toRightDerivedZero.app M ≫ (F.rightDerivedSingleHomologyIso 0).hom.app M := rfl
    _ = F.toRightDerivedZero.app M ≫
        (InjectiveResolution.isoRightDerivedSingleHomology F I 0).hom :=
      congrArg (fun k => F.toRightDerivedZero.app M ≫ k)
        (F.rightDerivedSingleHomologyIso_hom_app I 0)
    _ = (F.toRightDerivedZero.app M ≫ (I.isoRightDerivedObjCochain F 0).hom) ≫
        P.inv ≫ e := rfl
    _ = (I.toRightDerivedZeroCochainCycles F ≫
        (moduleResolutionSectionComplex X α I).homologyπ 0) ≫ P.inv ≫ e :=
      congrArg (fun k => k ≫ P.inv ≫ e)
        (I.toRightDerivedZero_comp_isoRightDerivedObjCochain F)
    _ = _ := rfl

private theorem zeroCycle_sectionHom (M : X.Modules) (I : InjectiveResolution M)
    (s : (moduleGlobalSectionsFunctorOfHom X α).obj M) :
    moduleResolutionSectionHom X α I 0
        ((moduleResolutionSectionCyclesIso X α I 0).hom
          (I.toRightDerivedZeroCochainCycles (moduleGlobalSectionsFunctorOfHom X α) s)) =
      (Scheme.Modules.unitHomGlobalSectionsEquiv X M).symm s ≫ I.ι.f 0 := by
  let F := moduleGlobalSectionsFunctorOfHom X α
  let K := moduleResolutionSectionComplex X α I
  let c := I.toRightDerivedZeroCochainCycles F s
  let z := (moduleResolutionSectionCyclesIso X α I 0).hom c
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let g : O ⟶ M := (Scheme.Modules.unitHomGlobalSectionsEquiv X M).symm s
  let f : O ⟶ I.cochainComplex.X 0 :=
    (Scheme.Modules.unitHomGlobalSectionsEquiv X (I.cochainComplex.X 0)).symm z.val
  have hf : Scheme.Modules.unitHomGlobalSectionsEquiv X (I.cochainComplex.X 0) f = z.val :=
    Equiv.apply_symm_apply _ _
  have hg : Scheme.Modules.unitHomGlobalSectionsEquiv X M g = s :=
    Equiv.apply_symm_apply _ _
  have hc : K.iCycles 0 c =
      F.map (I.cochainComplexXIso 0 0 rfl).inv (F.map (I.ι.f 0) s) :=
    congrArg (fun k : F.obj M ⟶ K.X 0 => k s)
      (I.toRightDerivedZeroCochainCycles_comp_iCycles F)
  have hleft : Scheme.Modules.unitHomGlobalSectionsEquiv X (I.cocomplex.X 0)
      (moduleResolutionSectionHom X α I 0 z) =
      F.map (I.cochainComplexXIso 0 0 rfl).hom z.val :=
    (Scheme.Modules.unitHomGlobalSectionsEquiv_naturality X f
      (I.cochainComplexXIso 0 0 rfl).hom).trans
        (congrArg (F.map (I.cochainComplexXIso 0 0 rfl).hom) hf)
  have hright : Scheme.Modules.unitHomGlobalSectionsEquiv X (I.cocomplex.X 0)
      (g ≫ I.ι.f 0) = F.map (I.ι.f 0) s :=
    (Scheme.Modules.unitHomGlobalSectionsEquiv_naturality X g (I.ι.f 0)).trans
      (congrArg (F.map (I.ι.f 0)) hg)
  have hi : F.map (I.cochainComplexXIso 0 0 rfl).inv ≫
      F.map (I.cochainComplexXIso 0 0 rfl).hom = 𝟙 _ :=
    (F.mapIso (I.cochainComplexXIso 0 0 rfl)).inv_hom_id
  apply (Scheme.Modules.unitHomGlobalSectionsEquiv X (I.cocomplex.X 0)).injective
  exact hleft.trans
    ((congrArg (F.map (I.cochainComplexXIso 0 0 rfl).hom)
      ((moduleResolutionSectionCyclesIso_hom_val X α I 0 c).trans hc)).trans
        ((congrArg (fun k => k (F.map (I.ι.f 0) s)) hi).trans hright.symm))

private theorem moduleDerivedZeroClass (M : X.Modules) (I : InjectiveResolution M)
    (s : (moduleGlobalSectionsFunctorOfHom X α).obj M) :
    let := moduleCohomologyModuleOfHom X α M 0
    moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I 0
        ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedSingleHomologyZeroIso.inv.app M s) =
      moduleExtCohomologyMap X M 0
        (Ext.mk₀ ((Scheme.Modules.unitHomGlobalSectionsEquiv X M).symm s)) := by
  let := moduleCohomologyModuleOfHom X α M 0
  let F := moduleGlobalSectionsFunctorOfHom X α
  let c := I.toRightDerivedZeroCochainCycles F s
  let z := (moduleResolutionSectionCyclesIso X α I 0).hom c
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let g : O ⟶ M := (Scheme.Modules.unitHomGlobalSectionsEquiv X M).symm s
  let ι₀ : M ⟶ I.cocomplex.X 0 := I.ι.f 0
  have hι₀ : ι₀ ≫ I.cocomplex.d 0 1 = 0 := I.ι_f_zero_comp_complex_d
  have ha : (g ≫ ι₀) ≫ I.cocomplex.d 0 1 = 0 :=
    (Category.assoc g ι₀ (I.cocomplex.d 0 1)).trans
      ((congrArg (fun k : M ⟶ I.cocomplex.X 1 => g ≫ k) hι₀).trans (comp_zero : g ≫ 0 = 0))
  have hExt : moduleResolutionSectionExtClass X α I 0 z = Ext.mk₀ g := by
    have hmk :
        (I.extMk (moduleResolutionSectionHom X α I 0 z) 1 rfl
          (moduleResolutionSectionHom_comp_d X α I 0 z) : Ext.{u + 1} O M 0) =
        I.extMk (g ≫ ι₀) 1 rfl ha := by
      congr 1
      exact zeroCycle_sectionHom X α M I s
    have hbase : (I.extMk (g ≫ ι₀) 1 rfl ha : Ext.{u + 1} O M 0) = Ext.mk₀ g :=
      I.extMk_ι_zero g
    exact (moduleResolutionSectionExtClass_eq_extMk X α I 0 z).trans (hmk.trans hbase)
  have hz : F.rightDerivedSingleHomologyZeroIso.inv.app M s =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
        (I.rightDerivedFunctorPlusIso F).hom
        ((DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) 0).inv.app
          (F.mapCochainComplexPlus.obj I.cochainComplexPlus)
          ((moduleResolutionSectionComplex X α I).homologyπ 0 c)) :=
    congrArg (fun k : F.obj M ⟶
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) =>
      k s) (zeroComparison_inv_resolution X α M I)
  calc
    _ = moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I 0
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
          (I.rightDerivedFunctorPlusIso F).hom
          ((DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) 0).inv.app
            (F.mapCochainComplexPlus.obj I.cochainComplexPlus)
            ((moduleResolutionSectionComplex X α I).homologyπ 0 c))) :=
      congrArg (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I 0) hz
    _ = moduleResolutionSectionClass X α I 0 z :=
      moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_homologyπ X α I 0 c
    _ = moduleExtCohomologyMap X M 0 (moduleResolutionSectionExtClass X α I 0 z) :=
      moduleResolutionSectionClass_apply X α I 0 z
    _ = _ := congrArg (moduleExtCohomologyMap X M 0) hExt

/-- The old original Sheaf.H section comparison agrees with the actual
left-exact derived-zero comparison on every original homology class. -/
theorem moduleDerivedGlobalSections_homology_zero_sections
    (M : X.Modules) (I : InjectiveResolution M)
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).obj
      ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))) :
    let := moduleCohomologyModuleOfHom X α M 0
    moduleH0EquivOfHom X α M
        (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I 0 x) =
      (moduleGlobalSectionsFunctorOfHom X α).rightDerivedSingleHomologyZeroIso.hom.app M x := by
  let := moduleCohomologyModuleOfHom X α M 0
  let E := (moduleGlobalSectionsFunctorOfHom X α).rightDerivedSingleHomologyZeroIso.app M
  let s := E.hom x
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let g : O ⟶ M := (Scheme.Modules.unitHomGlobalSectionsEquiv X M).symm s
  have hx : E.inv s = x :=
    congrArg (fun k => k x) E.hom_inv_id
  have he : moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I 0 x =
      moduleExtCohomologyMap X M 0 (Ext.mk₀ g) :=
    (congrArg (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I 0) hx.symm).trans
      (moduleDerivedZeroClass X α M I s)
  have hsections : moduleH0EquivOfHom X α M (moduleExtCohomologyMap X M 0 (Ext.mk₀ g)) = s :=
    (moduleH0EquivOfHom_extMk₀ X α M g).trans (Equiv.apply_symm_apply _ _)
  exact (congrArg (moduleH0EquivOfHom X α M) he).trans hsections

private theorem plusQ_shifted_full
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K L : CochainComplex.Plus C} (t : ShiftedHom K L (1 : ℤ)) :
    (t.map DerivedCategory.Plus.Q).map DerivedCategory.Plus.ι =
      (t.map (CochainComplex.Plus.ι C)).map DerivedCategory.Q := by
  let f : ShiftedHom (DerivedCategory.Q.obj K.obj) (DerivedCategory.Q.obj L.obj) (1 : ℤ) :=
    (t.map DerivedCategory.Plus.Q).map DerivedCategory.Plus.ι
  let g : ShiftedHom (DerivedCategory.Q.obj K.obj) (DerivedCategory.Q.obj L.obj) (1 : ℤ) :=
    (t.map (CochainComplex.Plus.ι C)).map DerivedCategory.Q
  have h := ShiftedHom.map_naturality t (DerivedCategory.Plus.QCompιIso C).hom
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_map,
    DerivedCategory.Plus.QCompιIso_hom_app] at h
  change f ≫ (𝟙 (DerivedCategory.Q.obj L.obj))⟦(1 : ℤ)⟧' =
    𝟙 (DerivedCategory.Q.obj K.obj) ≫ g at h
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] using h

private def resolutionCocyclePlus {M N : X.Modules} (I : InjectiveResolution N)
    (c : Cocycle ((CochainComplex.singleFunctor X.Modules 0).obj M) I.cochainComplex 1) :
    ShiftedHom ((CochainComplex.singleFunctorPlus X.Modules 0).obj M)
      I.cochainComplexPlus (1 : ℤ) := by
  let K := (CochainComplex.singleFunctorPlus X.Modules 0).obj M
  let L := I.cochainComplexPlus
  let f : K.obj ⟶ L.obj⟦(1 : ℤ)⟧ := Cocycle.equivHomShift.symm c
  exact ObjectProperty.homMk
    (f ≫ ((CochainComplex.Plus.ι X.Modules).commShiftIso (1 : ℤ)).inv.app L)

private theorem resolutionCocyclePlus_full {M N : X.Modules} (I : InjectiveResolution N)
    (c : Cocycle ((CochainComplex.singleFunctor X.Modules 0).obj M) I.cochainComplex 1) :
    (resolutionCocyclePlus X I c).map (CochainComplex.Plus.ι X.Modules) =
      Cocycle.equivHomShift.symm c := by
  let K := (CochainComplex.singleFunctorPlus X.Modules 0).obj M
  let L := I.cochainComplexPlus
  let f : K.obj ⟶ L.obj⟦(1 : ℤ)⟧ := Cocycle.equivHomShift.symm c
  let e : ((CategoryTheory.shiftFunctor (CochainComplex.Plus X.Modules) (1 : ℤ)).obj L).obj ≅
      L.obj⟦(1 : ℤ)⟧ := ((CochainComplex.Plus.ι X.Modules).commShiftIso (1 : ℤ)).app L
  change (f ≫ e.inv) ≫ e.hom = f
  exact (Category.assoc f e.inv e.hom).trans
    ((congrArg (fun k => f ≫ k) e.inv_hom_id).trans (Category.comp_id f))

private theorem resolutionCocyclePlus_Q_full {M N : X.Modules} (I : InjectiveResolution N)
    (c : Cocycle ((CochainComplex.singleFunctor X.Modules 0).obj M) I.cochainComplex 1) :
    ((resolutionCocyclePlus X I c).map DerivedCategory.Plus.Q).map DerivedCategory.Plus.ι =
      ShiftedHom.map (Cocycle.equivHomShift.symm c) DerivedCategory.Q := by
  calc
    _ = ((resolutionCocyclePlus X I c).map (CochainComplex.Plus.ι X.Modules)).map
        DerivedCategory.Q := plusQ_shifted_full (resolutionCocyclePlus X I c)
    _ = _ := congrArg (fun f => ShiftedHom.map f DerivedCategory.Q)
      (resolutionCocyclePlus_full X I c)

private theorem plusShiftedHom_map_injective
    {K L : DerivedCategory.Plus X.Modules}
    {f g : ShiftedHom K L (1 : ℤ)}
    (h : f.map DerivedCategory.Plus.ι = g.map DerivedCategory.Plus.ι) : f = g := by
  apply DerivedCategory.Plus.ι.map_injective
  exact (cancel_mono ((DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app L)).mp h

private theorem resolutionCocycle_ext_homPlus {M N : X.Modules} (I : InjectiveResolution N)
    (c : Cocycle ((CochainComplex.singleFunctor X.Modules 0).obj M) I.cochainComplex 1) :
    (I.extEquivCohomologyClass.symm (.mk c) : Ext.{u + 1} M N 1).homPlus =
      ((resolutionCocyclePlus X I c).map DerivedCategory.Plus.Q).comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl (inv (DerivedCategory.Plus.Q.map I.ιPlus)))
        (zero_add (1 : ℤ)) := by
  apply plusShiftedHom_map_injective X
  erw [Ext.homPlus_map, ShiftedHom.map_comp, ShiftedHom.map_mk₀,
    resolutionCocyclePlus_Q_full]
  let r : DerivedCategory.Q.obj I.cochainComplex ⟶
      (DerivedCategory.singleFunctor X.Modules 0).obj N :=
    DerivedCategory.Plus.ι.map (inv (DerivedCategory.Plus.Q.map I.ιPlus))
  change (I.extEquivCohomologyClass.symm (.mk c) : Ext.{u + 1} M N 1).hom =
    (ShiftedHom.map (Cocycle.equivHomShift.symm c) DerivedCategory.Q).comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl r) (zero_add (1 : ℤ))
  have hr : r = inv (DerivedCategory.Q.map I.ι') := by
    dsimp only [r]
    erw [Functor.map_inv]; rfl
  rw [hr]
  rw [I.extEquivCohomologyClass_symm_mk_hom]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, ShiftedHom.mk₀_id_comp]
  let j : DerivedCategory.Q.obj I.cochainComplex ⟶
      (DerivedCategory.singleFunctor X.Modules 0).obj N := inv (DerivedCategory.Q.map I.ι')
  change (ShiftedHom.map (Cocycle.equivHomShift.symm c) DerivedCategory.Q).comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl
        (j ≫ 𝟙 ((DerivedCategory.singleFunctor X.Modules 0).obj N))) (zero_add (1 : ℤ)) =
    (ShiftedHom.map (Cocycle.equivHomShift.symm c) DerivedCategory.Q).comp
      (ShiftedHom.mk₀ (0 : ℤ) rfl j) (zero_add (1 : ℤ))
  rw [Category.comp_id]

private def mappedResolutionCocycle {M N : X.Modules} (I : InjectiveResolution N)
    (c : Cocycle ((CochainComplex.singleFunctor X.Modules 0).obj M) I.cochainComplex 1) :
    ShiftedHom ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj
      ((moduleGlobalSectionsFunctorOfHom X α).obj M))
      (DerivedCategory.Plus.Q.obj
        ((moduleGlobalSectionsFunctorOfHom X α).mapCochainComplexPlus.obj
          I.cochainComplexPlus)) (1 : ℤ) :=
  DerivedCategory.Plus.Q.map
      (show (CochainComplex.singleFunctorPlus (ModuleCat.{u} R) 0).obj
          ((moduleGlobalSectionsFunctorOfHom X α).obj M) ⟶
        (moduleGlobalSectionsFunctorOfHom X α).mapCochainComplexPlus.obj
          ((CochainComplex.singleFunctorPlus X.Modules 0).obj M) from
        ObjectProperty.homMk ((singleMapHomologicalComplex
          (moduleGlobalSectionsFunctorOfHom X α) (.up ℤ) 0).inv.app M)) ≫
    ((resolutionCocyclePlus X I c).map
      (moduleGlobalSectionsFunctorOfHom X α).mapCochainComplexPlus).map DerivedCategory.Plus.Q

private theorem derivedUnit_resolutionCocycle {M N : X.Modules} (I : InjectiveResolution N)
    (c : Cocycle ((CochainComplex.singleFunctor X.Modules 0).obj M) I.cochainComplex 1) :
    (moduleGlobalSectionsFunctorOfHom X α).rightDerivedSingleUnit M ≫
        ((I.extEquivCohomologyClass.symm (.mk c) : Ext.{u + 1} M N 1).homPlus.map
          (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus) =
      mappedResolutionCocycle X α I c ≫
        (I.rightDerivedFunctorPlusIso (moduleGlobalSectionsFunctorOfHom X α)).hom⟦(1 : ℤ)⟧' := by
  let F := moduleGlobalSectionsFunctorOfHom X α
  let t := resolutionCocyclePlus X I c
  let a := (I.extEquivCohomologyClass.symm (.mk c) : Ext.{u + 1} M N 1).homPlus
  let p : DerivedCategory.Plus.Q.obj ((CochainComplex.singleFunctorPlus X.Modules 0).obj N) ⟶
      DerivedCategory.Plus.Q.obj I.cochainComplexPlus := DerivedCategory.Plus.Q.map I.ιPlus
  let q : ShiftedHom
      (DerivedCategory.Plus.Q.obj ((CochainComplex.singleFunctorPlus X.Modules 0).obj M))
      (DerivedCategory.Plus.Q.obj I.cochainComplexPlus) (1 : ℤ) := t.map DerivedCategory.Plus.Q
  let σ : (CochainComplex.singleFunctorPlus (ModuleCat.{u} R) 0).obj (F.obj M) ⟶
      F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus X.Modules 0).obj M) :=
    ObjectProperty.homMk ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)
  have hq : mappedResolutionCocycle X α I c = DerivedCategory.Plus.Q.map σ ≫
      (t.map F.mapCochainComplexPlus).map DerivedCategory.Plus.Q := rfl
  have ha : a.comp (ShiftedHom.mk₀ (0 : ℤ) rfl p) (zero_add (1 : ℤ)) =
      t.map DerivedCategory.Plus.Q := by
    dsimp only [a, t, p]
    erw [resolutionCocycle_ext_homPlus, ShiftedHom.comp_mk₀, ShiftedHom.comp_mk₀]
    change (q ≫ (inv p)⟦(1 : ℤ)⟧') ≫ p⟦(1 : ℤ)⟧' = q
    rw [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have haF : a.map F.rightDerivedFunctorPlus ≫
      (F.rightDerivedFunctorPlus.map p)⟦(1 : ℤ)⟧' =
      (t.map DerivedCategory.Plus.Q).map F.rightDerivedFunctorPlus := by
    have h := congrArg (fun f => f.map F.rightDerivedFunctorPlus) ha
    erw [ShiftedHom.map_comp, ShiftedHom.map_mk₀, ShiftedHom.comp_mk₀] at h
    exact h
  have hη := ShiftedHom.map_naturality t F.rightDerivedFunctorPlusUnit
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_map] at hη
  apply (cancel_mono ((F.rightDerivedFunctorPlus.map p)⟦(1 : ℤ)⟧')).mp
  change (F.rightDerivedSingleUnit M ≫ a.map F.rightDerivedFunctorPlus) ≫
      (F.rightDerivedFunctorPlus.map p)⟦(1 : ℤ)⟧' =
    (mappedResolutionCocycle X α I c ≫ (I.rightDerivedFunctorPlusIso F).hom⟦(1 : ℤ)⟧') ≫
      (F.rightDerivedFunctorPlus.map p)⟦(1 : ℤ)⟧'
  rw [Category.assoc, haF]
  change (DerivedCategory.Plus.Q.map σ ≫
      F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus X.Modules 0).obj M)) ≫
        (t.map DerivedCategory.Plus.Q).map F.rightDerivedFunctorPlus = _
  rw [Category.assoc, ← hη]
  have he : (I.rightDerivedFunctorPlusIso F).hom⟦(1 : ℤ)⟧' ≫
      (F.rightDerivedFunctorPlus.map p)⟦(1 : ℤ)⟧' =
      (F.rightDerivedFunctorPlusUnit.app I.cochainComplexPlus)⟦(1 : ℤ)⟧' := by
    let Sh := CategoryTheory.shiftFunctor (DerivedCategory.Plus (ModuleCat.{u} R)) (1 : ℤ)
    have h := congrArg Sh.map (I.rightDerivedFunctorPlusIso_hom_comp F)
    simpa only [Functor.map_comp] using h
  have hrhs : (mappedResolutionCocycle X α I c ≫
      (I.rightDerivedFunctorPlusIso F).hom⟦(1 : ℤ)⟧') ≫
      (F.rightDerivedFunctorPlus.map p)⟦(1 : ℤ)⟧' =
      mappedResolutionCocycle X α I c ≫
        (F.rightDerivedFunctorPlusUnit.app I.cochainComplexPlus)⟦(1 : ℤ)⟧' := by
    rw [Category.assoc, he]
  let U := (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (F.obj M)
  let V := DerivedCategory.Plus.Q.obj
    (F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus X.Modules 0).obj M))
  let J := DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj I.cochainComplexPlus)
  let W := F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj I.cochainComplexPlus)
  let s : U ⟶ V := DerivedCategory.Plus.Q.map σ
  let v : ShiftedHom V J (1 : ℤ) :=
    (t.map F.mapCochainComplexPlus).map DerivedCategory.Plus.Q
  let k : ShiftedHom U J (1 : ℤ) := mappedResolutionCocycle X α I c
  let h : J ⟶ W := F.rightDerivedFunctorPlusUnit.app I.cochainComplexPlus
  have hk : k = s ≫ v := hq
  have hl : s ≫ v ≫ h⟦(1 : ℤ)⟧' = k ≫ h⟦(1 : ℤ)⟧' :=
    (Category.assoc s v (h⟦(1 : ℤ)⟧')).symm.trans
      (congrArg (fun q : ShiftedHom U J (1 : ℤ) => q ≫ h⟦(1 : ℤ)⟧') hk.symm)
  have hr : (k ≫ (I.rightDerivedFunctorPlusIso F).hom⟦(1 : ℤ)⟧') ≫
      (F.rightDerivedFunctorPlus.map p)⟦(1 : ℤ)⟧' = k ≫ h⟦(1 : ℤ)⟧' := hrhs
  change s ≫ v ≫ h⟦(1 : ℤ)⟧' =
    (k ≫ (I.rightDerivedFunctorPlusIso F).hom⟦(1 : ℤ)⟧') ≫
      (F.rightDerivedFunctorPlus.map p)⟦(1 : ℤ)⟧'
  exact hl.trans hr.symm

private theorem plus_homology_shiftMap_full
    {K L : DerivedCategory.Plus (ModuleCat.{u} R)} (t : ShiftedHom K L (1 : ℤ)) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).shiftMap
        t (0 : ℤ) (1 : ℤ) (by omega) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).shiftMap
        (t.map DerivedCategory.Plus.ι) (0 : ℤ) (1 : ℤ) (by omega) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0
  let ι : DerivedCategory.Plus (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
    DerivedCategory.Plus.ι
  let c : (L⟦(1 : ℤ)⟧).obj ⟶ L.obj⟦(1 : ℤ)⟧ := (ι.commShiftIso (1 : ℤ)).hom.app L
  let e : H.obj (L.obj⟦(1 : ℤ)⟧) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 1).obj L.obj :=
    (H.shiftIso (1 : ℤ) (0 : ℤ) (1 : ℤ) (by omega)).app L.obj
  change H.map t.hom ≫ (𝟙 _ ≫ H.map c ≫ 𝟙 _ ≫ e.hom) =
    H.map (t.hom ≫ c) ≫ e.hom
  simp only [Category.id_comp, Functor.map_comp, Category.assoc]

private theorem plus_homologyFactors_hom (K : CochainComplex.Plus (ModuleCat.{u} R)) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) n).hom.app K =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).hom.app K.obj := by
  let Z : CochainComplex (ModuleCat.{u} R) ℤ := K.obj
  let W := DerivedCategory.Q.obj Z
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) n
  let h : H.obj W ⟶ Z.homology n :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).hom.app Z
  let P : H.obj W ≅ Z.homology n :=
    (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) n).app K
  have hp : P.hom = 𝟙 (H.obj W) ≫ H.map (𝟙 W) ≫ 𝟙 (H.obj W) ≫ h := rfl
  change P.hom = h
  exact hp.trans (by simp only [CategoryTheory.Functor.map_id, Category.id_comp])

private theorem plus_homologyFactors_inv (K : CochainComplex.Plus (ModuleCat.{u} R)) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) n).inv.app K =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).inv.app K.obj := by
  let Z : CochainComplex (ModuleCat.{u} R) ℤ := K.obj
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) n
  let P : H.obj (DerivedCategory.Q.obj Z) ≅ Z.homology n :=
    (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) n).app K
  let E : H.obj (DerivedCategory.Q.obj Z) ≅ Z.homology n :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).app Z
  have h : P.hom = E.hom := plus_homologyFactors_hom K n
  change P.inv = E.inv
  exact congrArg (fun e : H.obj (DerivedCategory.Q.obj Z) ≅ Z.homology n => e.inv) (Iso.ext h)

private theorem plus_homology_shiftMap_Q
    {K L : CochainComplex.Plus (ModuleCat.{u} R)} (t : ShiftedHom K L (1 : ℤ)) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).shiftMap
        (t.map DerivedCategory.Plus.Q) (0 : ℤ) (1 : ℤ) (by omega) =
      (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) 0).hom.app K ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
          (t.map (CochainComplex.Plus.ι (ModuleCat.{u} R))) (0 : ℤ) (1 : ℤ) (by omega) ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) 1).inv.app L := by
  rw [plus_homology_shiftMap_full, plusQ_shifted_full,
    plus_homologyFactors_hom, plus_homologyFactors_inv]
  change (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).shiftMap
      ((t.map (CochainComplex.Plus.ι (ModuleCat.{u} R))).map DerivedCategory.Q)
      (0 : ℤ) (1 : ℤ) (by omega) =
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) 0).hom.app K.obj ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
        (t.map (CochainComplex.Plus.ι (ModuleCat.{u} R))) (0 : ℤ) (1 : ℤ) (by omega) ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) 1).inv.app L.obj
  exact DerivedCategory.shiftMap_homologyFunctor_map_Q
    (t.map (CochainComplex.Plus.ι (ModuleCat.{u} R))) (0 : ℤ) (1 : ℤ) (by omega)

private theorem single_homology_comparison (V : ModuleCat.{u} R) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).hom.app V =
      (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) 0).hom.app
          ((CochainComplex.singleFunctorPlus (ModuleCat.{u} R) 0).obj V) ≫
        (singleObjHomologySelfIso (.up ℤ) 0 V).hom := by
  dsimp [DerivedCategory.singleFunctorCompHomologyFunctorIso,
    DerivedCategory.Plus.homologyFunctorFactors,
    DerivedCategory.singleFunctorsPostcompQIso, DerivedCategory.Plus.QCompιIso,
    ObjectProperty.liftCompιIso]
  let Z := (single (ModuleCat.{u} R) (.up ℤ) 0).obj V
  let W := DerivedCategory.Q.obj Z
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0
  let h : H.obj W ⟶ Z.homology 0 :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) 0).hom.app Z
  let e : Z.homology 0 ⟶ V := (singleObjHomologySelfIso (.up ℤ) 0 V).hom
  change H.map (𝟙 W) ≫ 𝟙 (H.obj W) ≫ h ≫ e =
    (𝟙 (H.obj W) ≫ H.map (𝟙 W) ≫ 𝟙 (H.obj W) ≫ h) ≫ e
  simp only [Category.id_comp]
  exact (Category.assoc (H.map (𝟙 W)) h e).symm

private theorem single_to_Q_homology (V : ModuleCat.{u} R)
    (K : CochainComplex.Plus (ModuleCat.{u} R))
    (τ : (CochainComplex.singleFunctorPlus (ModuleCat.{u} R) 0).obj V ⟶ K) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).inv.app V ≫
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
          (DerivedCategory.Plus.Q.map τ) ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) 0).hom.app K =
      (singleObjHomologySelfIso (.up ℤ) 0 V).inv ≫ homologyMap τ.hom 0 := by
  let S := (CochainComplex.singleFunctorPlus (ModuleCat.{u} R) 0).obj V
  let P : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).obj
      (DerivedCategory.Plus.Q.obj S) ≅
      ((single (ModuleCat.{u} R) (.up ℤ) 0).obj V).homology 0 :=
    (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) 0).app S
  have hE : (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).inv.app V =
      (singleObjHomologySelfIso (.up ℤ) 0 V).inv ≫ P.inv := by
    let E : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).obj
        (DerivedCategory.Plus.Q.obj S) ≅ V :=
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app V
    let e : ((single (ModuleCat.{u} R) (.up ℤ) 0).obj V).homology 0 ≅ V :=
      singleObjHomologySelfIso (.up ℤ) 0 V
    have h : E.hom = (P ≪≫ e).hom := single_homology_comparison V
    change E.inv = e.inv ≫ P.inv
    exact congrArg (fun i : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).obj
      (DerivedCategory.Plus.Q.obj S) ≅ V => i.inv) (Iso.ext h)
  have hP := (DerivedCategory.Plus.homologyFunctorFactors
    (A := ModuleCat.{u} R) 0).hom.naturality τ
  change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
      (DerivedCategory.Plus.Q.map τ) ≫
      (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) 0).hom.app K =
    P.hom ≫ homologyMap τ.hom 0 at hP
  erw [hE, Category.assoc, hP, Iso.inv_hom_id_assoc]; rfl

private theorem single_shifted_homology_from_component
    (V : ModuleCat.{u} R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (t : (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj V ⟶ K⟦(1 : ℤ)⟧)
    (f : V ⟶ K.X 1) (hf : f ≫ K.d 1 2 = 0)
    (hcomp : (singleObjXSelf (.up ℤ) 0 V).inv ≫ t.f 0 ≫
        (K.shiftFunctorObjXIso (1 : ℤ) (0 : ℤ) (1 : ℤ) (by omega)).hom = f) :
    (singleObjHomologySelfIso (.up ℤ) 0 V).inv ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftMap
          t (0 : ℤ) (1 : ℤ) (by omega) =
      K.liftCycles f 2 (by simp) hf ≫ K.homologyπ 1 := by
  let Z := K⟦(1 : ℤ)⟧
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
          (((single (ModuleCat.{u} R) (.up ℤ) 0).obj V).iCycles 0 ≫ t.f 0) :=
        congrArg (fun k => (singleObjCyclesSelfIso (.up ℤ) 0 V).inv ≫ k) (cyclesMap_i t 0)
      _ = f₀ := singleObjCyclesSelfIso_inv_iCycles_assoc (.up ℤ) 0 V (t.f 0)
      _ = _ := (Z.liftCycles_i f₀ 1 (by simp) hf₀).symm
  have hh : (singleObjHomologySelfIso (.up ℤ) 0 V).inv ≫ homologyMap t 0 =
      z ≫ Z.homologyπ 0 := by
    rw [← singleObjCyclesSelfIso_inv_homologyπ]
    simp only [Category.assoc, homologyπ_naturality]
    rw [← Category.assoc, hz]
  let E : Z.homology 0 ≅ K.homology 1 :=
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftIso
      (1 : ℤ) (0 : ℤ) (1 : ℤ) (by omega)).app K
  let f' : V ⟶ K.X 1 := f₀ ≫
    (K.shiftFunctorObjXIso (1 : ℤ) (0 : ℤ) (1 : ℤ) (by omega)).hom
  have hff : f' = f := hcomp
  have hf' : f' ≫ K.d 1 2 = 0 := (congrArg (fun k => k ≫ K.d 1 2) hff).trans hf
  have hshift : z ≫ Z.homologyπ 0 =
      K.liftCycles f' 2 (by simp) hf' ≫ K.homologyπ 1 ≫ E.inv :=
    CochainComplex.liftCycles_shift_homologyπ K f₀ 1 (by simp) hf₀
      1 (by omega) 2 (by simp)
  change ((singleObjHomologySelfIso (.up ℤ) 0 V).inv ≫ homologyMap t 0) ≫ E.hom = _
  calc
    _ = (z ≫ Z.homologyπ 0) ≫ E.hom := congrArg (fun k => k ≫ E.hom) hh
    _ = (K.liftCycles f' 2 (by simp) hf' ≫ K.homologyπ 1 ≫ E.inv) ≫ E.hom :=
      congrArg (fun k => k ≫ E.hom) hshift
    _ = K.liftCycles f' 2 (by simp) hf' ≫ K.homologyπ 1 := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := by
      congr 1
      apply (cancel_mono (K.iCycles 1)).mp
      exact (K.liftCycles_i f' 2 (by simp) hf').trans
        (hff.trans (K.liftCycles_i f 2 (by simp) hf).symm)

private theorem resolutionCocyclePlus_map_full {M N : X.Modules} (I : InjectiveResolution N)
    (c : Cocycle ((CochainComplex.singleFunctor X.Modules 0).obj M) I.cochainComplex 1) :
    ((resolutionCocyclePlus X I c).map
        (moduleGlobalSectionsFunctorOfHom X α).mapCochainComplexPlus).map
          (CochainComplex.Plus.ι (ModuleCat.{u} R)) =
      ShiftedHom.map (Cocycle.equivHomShift.symm c)
        ((moduleGlobalSectionsFunctorOfHom X α).mapHomologicalComplex (.up ℤ)) := by
  let F := moduleGlobalSectionsFunctorOfHom X α
  let K : CochainComplex X.Modules ℤ := (CochainComplex.singleFunctor X.Modules 0).obj M
  let L : CochainComplex X.Modules ℤ := I.cochainComplex
  let f : ShiftedHom ((F.mapHomologicalComplex (.up ℤ)).obj K)
      ((F.mapHomologicalComplex (.up ℤ)).obj L) (1 : ℤ) :=
    ((resolutionCocyclePlus X I c).map F.mapCochainComplexPlus).map
      (CochainComplex.Plus.ι (ModuleCat.{u} R))
  let g : ShiftedHom ((F.mapHomologicalComplex (.up ℤ)).obj K)
      ((F.mapHomologicalComplex (.up ℤ)).obj L) (1 : ℤ) :=
    ShiftedHom.map (Cocycle.equivHomShift.symm c) (F.mapHomologicalComplex (.up ℤ))
  have h := ShiftedHom.map_naturality (resolutionCocyclePlus X I c)
    F.mapCochainComplexPlusCompι.hom
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_map,
    Functor.mapCochainComplexPlusCompι_hom_app, resolutionCocyclePlus_full] at h
  change f ≫ (𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj L))⟦(1 : ℤ)⟧' =
    𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫ g at h
  change f = g
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] using h

private theorem fromSingleCocycle_component {M N : X.Modules} (I : InjectiveResolution N)
    (f : M ⟶ I.cochainComplex.X 1) (hf : f ≫ I.cochainComplex.d 1 2 = 0) :
    (singleObjXSelf (.up ℤ) 0 M).inv ≫
        (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk f (zero_add (1 : ℤ)) 2 rfl hf)).f 0 ≫
        (I.cochainComplex.shiftFunctorObjXIso (1 : ℤ) (0 : ℤ) (1 : ℤ) (by omega)).hom = f := by
  simp only [Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f, Cocycle.rightShift_coe]
  rw [Cochain.rightShift_v _ 1 0 (zero_add (1 : ℤ)) 0 0 (add_zero 0) 1 rfl]
  simp only [Cocycle.fromSingleMk_coe, Cochain.fromSingleMk_v,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

private theorem sectionComplex_cycle_condition {M N : X.Modules} (I : InjectiveResolution N)
    (f : M ⟶ I.cochainComplex.X 1) (hf : f ≫ I.cochainComplex.d 1 2 = 0) :
    (moduleGlobalSectionsFunctorOfHom X α).map f ≫
      (moduleResolutionSectionComplex X α I).d 1 2 = 0 := by
  let F := moduleGlobalSectionsFunctorOfHom X α
  change F.map f ≫ F.map (I.cochainComplex.d 1 2) = 0
  exact (F.map_comp f (I.cochainComplex.d 1 2)).symm.trans
    ((congrArg F.map hf).trans (F.map_zero M (I.cochainComplex.X 2)))

private theorem mappedResolutionCocycle_homology {M N : X.Modules} (I : InjectiveResolution N)
    (f : M ⟶ I.cochainComplex.X 1) (hf : f ≫ I.cochainComplex.d 1 2 = 0) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).inv.app
        ((moduleGlobalSectionsFunctorOfHom X α).obj M) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).shiftMap
        (mappedResolutionCocycle X α I
          (Cocycle.fromSingleMk f (zero_add (1 : ℤ)) 2 rfl hf)) (0 : ℤ) (1 : ℤ) (by omega) ≫
      (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) 1).hom.app
        ((moduleGlobalSectionsFunctorOfHom X α).mapCochainComplexPlus.obj I.cochainComplexPlus) =
    (moduleResolutionSectionComplex X α I).liftCycles
        ((moduleGlobalSectionsFunctorOfHom X α).map f) 2 (by simp)
        (sectionComplex_cycle_condition X α I f hf) ≫
      (moduleResolutionSectionComplex X α I).homologyπ 1 := by
  let F := moduleGlobalSectionsFunctorOfHom X α
  let c := Cocycle.fromSingleMk f (zero_add (1 : ℤ)) 2 rfl hf
  let K := F.mapCochainComplexPlus.obj I.cochainComplexPlus
  let L := F.mapCochainComplexPlus.obj
    ((CochainComplex.singleFunctorPlus X.Modules 0).obj M)
  let τ : (CochainComplex.singleFunctorPlus (ModuleCat.{u} R) 0).obj (F.obj M) ⟶ L :=
    ObjectProperty.homMk ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)
  let t := (resolutionCocyclePlus X I c).map F.mapCochainComplexPlus
  let Kfull : CochainComplex (ModuleCat.{u} R) ℤ := moduleResolutionSectionComplex X α I
  let Lfull : CochainComplex (ModuleCat.{u} R) ℤ :=
    (F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor X.Modules 0).obj M)
  let τfull : (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (F.obj M) ⟶ Lfull :=
    (singleMapHomologicalComplex F (.up ℤ) 0).inv.app M
  let tFull : ShiftedHom Lfull Kfull (1 : ℤ) :=
    t.map (CochainComplex.Plus.ι (ModuleCat.{u} R))
  have ht : tFull = ShiftedHom.map (Cocycle.equivHomShift.symm c)
      (F.mapHomologicalComplex (.up ℤ)) := resolutionCocyclePlus_map_full X α I c
  have hcomp : (singleObjXSelf (.up ℤ) 0 (F.obj M)).inv ≫ (τfull ≫ tFull).f 0 ≫
      (Kfull.shiftFunctorObjXIso (1 : ℤ) (0 : ℤ) (1 : ℤ) (by omega)).hom = F.map f := by
    rw [ht]
    change (singleObjXSelf (.up ℤ) 0 (F.obj M)).inv ≫
        ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M ≫
          ShiftedHom.map (Cocycle.equivHomShift.symm c)
            (F.mapHomologicalComplex (.up ℤ))).f 0 ≫
        (CochainComplex.shiftFunctorObjXIso
          ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)
          (1 : ℤ) (0 : ℤ) (1 : ℤ) (by omega)).hom = F.map f
    simp only [HomologicalComplex.comp_f, ShiftedHom.map,
      singleMapHomologicalComplex_inv_app_self, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Category.assoc, Iso.inv_hom_id_assoc, CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
    let e : M ⟶ ((CochainComplex.singleFunctor X.Modules 0).obj M).X 0 :=
      (singleObjXSelf (.up ℤ) 0 M).inv
    let r : ((CochainComplex.singleFunctor X.Modules 0).obj M).X 0 ⟶
        I.cochainComplex.X 1 := (Cocycle.equivHomShift.symm c).f 0
    let a : M ⟶ I.cochainComplex.X 1 := e ≫ r
    have ha : a = f := by
      have h := fromSingleCocycle_component X I f hf
      change a ≫ 𝟙 (I.cochainComplex.X 1) = f at h
      exact (Category.comp_id a).symm.trans h
    change F.map e ≫ F.map r ≫ 𝟙 (F.obj (I.cochainComplex.X 1)) ≫
      𝟙 (F.obj (I.cochainComplex.X 1)) = F.map f
    simp only [Category.comp_id]
    exact (F.map_comp e r).symm.trans (congrArg F.map ha)
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0
  let Hc := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0
  let P₀ : H.obj (DerivedCategory.Plus.Q.obj L) ≅ Lfull.homology 0 :=
    (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) 0).app L
  let P₁ : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 1).obj
      (DerivedCategory.Plus.Q.obj K) ≅ Kfull.homology 1 :=
    (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) 1).app K
  let e₀ : F.obj M ⟶
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (F.obj M)).homology 0 :=
    (singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).inv
  let t₀ : Lfull.homology 0 ⟶ Kfull.homology 1 :=
    Hc.shiftMap tFull (0 : ℤ) (1 : ℤ) (by omega)
  let τt₀ : ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (F.obj M)).homology 0 ⟶
      Kfull.homology 1 := Hc.shiftMap (τfull ≫ tFull) (0 : ℤ) (1 : ℤ) (by omega)
  let l : F.obj M ⟶ Kfull.cycles 1 :=
    Kfull.liftCycles (F.map f) 2 (by simp) (sectionComplex_cycle_condition X α I f hf)
  let d₀ : F.obj M ⟶ H.obj (DerivedCategory.Plus.Q.obj
      ((CochainComplex.singleFunctorPlus (ModuleCat.{u} R) 0).obj (F.obj M))) :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).inv.app (F.obj M)
  have hsingle : d₀ ≫ H.map (DerivedCategory.Plus.Q.map τ) ≫ P₀.hom =
      e₀ ≫ homologyMap τfull 0 :=
    single_to_Q_homology (R := R) (F.obj M) L τ
  have hshift : homologyMap τfull 0 ≫ t₀ = τt₀ :=
    (Hc.shiftMap_comp' τfull tFull (0 : ℤ) (1 : ℤ) (by omega)).symm
  have hfinal : e₀ ≫ τt₀ = l ≫ Kfull.homologyπ 1 :=
    single_shifted_homology_from_component (R := R) (F.obj M) Kfull
      (τfull ≫ tFull) (F.map f) (sectionComplex_cycle_condition X α I f hf) hcomp
  change d₀ ≫
      H.shiftMap (DerivedCategory.Plus.Q.map τ ≫ t.map DerivedCategory.Plus.Q)
        (0 : ℤ) (1 : ℤ) (by omega) ≫ P₁.hom = l ≫ Kfull.homologyπ 1
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

private theorem resolutionSectionCocycle_precomp {M N : X.Modules} (I : InjectiveResolution N)
    (f : M ⟶ I.cochainComplex.X 1) (hf : f ≫ I.cochainComplex.d 1 2 = 0)
    (s : (moduleGlobalSectionsFunctorOfHom X α).obj M) :
    let F := moduleGlobalSectionsFunctorOfHom X α
    let K := moduleResolutionSectionComplex X α I
    let c := K.liftCycles (F.map f) 2 (by simp) (sectionComplex_cycle_condition X α I f hf) s
    let z := (moduleResolutionSectionCyclesIso X α I 1).hom c
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let g : O ⟶ M := (Scheme.Modules.unitHomGlobalSectionsEquiv X M).symm s
    moduleResolutionSectionCocycle X α I 1 z =
      (Cocycle.fromSingleMk f (zero_add (1 : ℤ)) 2 rfl hf).precomp
        ((CochainComplex.singleFunctor X.Modules 0).map g) := by
  let F := moduleGlobalSectionsFunctorOfHom X α
  let K := moduleResolutionSectionComplex X α I
  let l := K.liftCycles (F.map f) 2 (by simp) (sectionComplex_cycle_condition X α I f hf)
  let c := l s
  let z := (moduleResolutionSectionCyclesIso X α I 1).hom c
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let g : O ⟶ M := (Scheme.Modules.unitHomGlobalSectionsEquiv X M).symm s
  have hcy : K.iCycles 1 c = F.map f s :=
    congrArg (fun k : F.obj M ⟶ K.X 1 => k s) (K.liftCycles_i (F.map f) 2 (by simp) _)
  have hz : z.val = F.map f s :=
    (moduleResolutionSectionCyclesIso_hom_val X α I 1 c).trans hcy
  have hg : Scheme.Modules.unitHomGlobalSectionsEquiv X M g = s :=
    Equiv.apply_symm_apply _ _
  have hn : Scheme.Modules.unitHomGlobalSectionsEquiv X (I.cochainComplex.X 1) (g ≫ f) =
      F.map f s :=
    (Scheme.Modules.unitHomGlobalSectionsEquiv_naturality X g f).trans
      (congrArg (F.map f) hg)
  have hhom : (Scheme.Modules.unitHomGlobalSectionsEquiv X (I.cochainComplex.X 1)).symm z.val =
      g ≫ f := by
    apply (Scheme.Modules.unitHomGlobalSectionsEquiv X (I.cochainComplex.X 1)).injective
    exact (Equiv.apply_symm_apply _ _).trans (hz.trans hn.symm)
  have hc : moduleResolutionSectionCocycle X α I 1 z =
      Cocycle.fromSingleMk (g ≫ f) (zero_add (1 : ℤ)) 2 rfl (by
        rw [Category.assoc, hf, comp_zero]) := by
    apply Cocycle.ext
    change Cochain.fromSingleMk (C := X.Modules)
        ((Scheme.Modules.unitHomGlobalSectionsEquiv X (I.cochainComplex.X 1)).symm z.val)
        (zero_add (1 : ℤ)) =
      Cochain.fromSingleMk (C := X.Modules) (g ≫ f) (zero_add (1 : ℤ))
    exact congrArg (fun k : O ⟶ I.cochainComplex.X 1 =>
      Cochain.fromSingleMk (C := X.Modules) k (zero_add (1 : ℤ))) hhom
  exact hc.trans (Cocycle.fromSingleMk_precomp g f (zero_add (1 : ℤ)) 2 rfl hf)

private theorem derivedSections_extAction_fromSingle {M N : X.Modules} (I : InjectiveResolution N)
    (f : M ⟶ I.cochainComplex.X 1) (hf : f ≫ I.cochainComplex.d 1 2 = 0)
    (s : (moduleGlobalSectionsFunctorOfHom X α).obj M) :
    let := moduleCohomologyModuleOfHom X α N 1
    let c := Cocycle.fromSingleMk f (zero_add (1 : ℤ)) 2 rfl hf
    let a : Ext.{u + 1} M N 1 := I.extEquivCohomologyClass.symm (.mk c)
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let g : O ⟶ M := (Scheme.Modules.unitHomGlobalSectionsEquiv X M).symm s
    moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I 1
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).shiftMap
        (a.homPlus.map (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus)
        (0 : ℤ) (1 : ℤ) (by omega)
        ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedSingleHomologyZeroIso.inv.app M s)) =
      moduleExtCohomologyMap X N 1 ((Ext.mk₀ g).comp a (Nat.zero_add 1)) := by
  let := moduleCohomologyModuleOfHom X α N 1
  let F := moduleGlobalSectionsFunctorOfHom X α
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0
  let H₁ := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 1
  let K := moduleResolutionSectionComplex X α I
  let J := F.mapCochainComplexPlus.obj I.cochainComplexPlus
  let QM := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)
  let QN := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj N)
  let QF := (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (F.obj M)
  let P : H₁.obj (DerivedCategory.Plus.Q.obj J) ≅ K.homology 1 :=
    (DerivedCategory.Plus.homologyFunctorFactors (A := ModuleCat.{u} R) 1).app J
  let e : DerivedCategory.Plus.Q.obj J ≅ QN := I.rightDerivedFunctorPlusIso F
  let c := Cocycle.fromSingleMk f (zero_add (1 : ℤ)) 2 rfl hf
  let a : Ext.{u + 1} M N 1 := I.extEquivCohomologyClass.symm (.mk c)
  let u : QF ⟶ QM := F.rightDerivedSingleUnit M
  let b : ShiftedHom QM QN (1 : ℤ) := a.homPlus.map F.rightDerivedFunctorPlus
  let A : H.obj QM ⟶ H₁.obj QN := H.shiftMap b (0 : ℤ) (1 : ℤ) (by omega)
  let q : ShiftedHom QF (DerivedCategory.Plus.Q.obj J) (1 : ℤ) :=
    mappedResolutionCocycle X α I c
  let E : DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0 ⋙ H ≅ 𝟭 (ModuleCat.{u} R) :=
    DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0
  let l := K.liftCycles (F.map f) 2 (by simp) (sectionComplex_cycle_condition X α I f hf)
  let z := (moduleResolutionSectionCyclesIso X α I 1).hom (l s)
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let g : O ⟶ M := (Scheme.Modules.unitHomGlobalSectionsEquiv X M).symm s
  have hq : E.inv.app (F.obj M) ≫ H.shiftMap q (0 : ℤ) (1 : ℤ) (by omega) =
      l ≫ K.homologyπ 1 ≫ P.inv := by
    apply (cancel_mono P.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact mappedResolutionCocycle_homology X α I f hf
  have hunit : u ≫ b = q ≫ e.hom⟦(1 : ℤ)⟧' :=
    derivedUnit_resolutionCocycle X α I c
  have hd : H.map u ≫ A =
      H.shiftMap q (0 : ℤ) (1 : ℤ) (by omega) ≫ H₁.map e.hom := by
    let hmap : ShiftedHom QF QN (1 : ℤ) → (H.obj QF ⟶ H₁.obj QN) :=
      fun k => H.shiftMap k (0 : ℤ) (1 : ℤ) (by omega)
    have h := congrArg hmap hunit
    change H.shiftMap (u ≫ b) (0 : ℤ) (1 : ℤ) (by omega) =
      H.shiftMap (q ≫ e.hom⟦(1 : ℤ)⟧') (0 : ℤ) (1 : ℤ) (by omega) at h
    erw [Functor.shiftMap_comp', Functor.shiftMap_comp] at h
    change H.map u ≫ A = H.shiftMap q (0 : ℤ) (1 : ℤ) (by omega) ≫ H₁.map e.hom at h
    exact h
  have hnorm : F.rightDerivedSingleHomologyZeroIso.inv.app M ≫ A =
      l ≫ K.homologyπ 1 ≫ P.inv ≫ H₁.map e.hom := by
    calc
      _ = (E.inv.app (F.obj M) ≫ H.map u) ≫ A :=
        congrArg (fun k : F.obj M ⟶ H.obj QM => k ≫ A)
          (F.rightDerivedSingleUnit_homology_zero M).symm
      _ = E.inv.app (F.obj M) ≫ (H.map u ≫ A) := Category.assoc _ _ _
      _ = E.inv.app (F.obj M) ≫
          (H.shiftMap q (0 : ℤ) (1 : ℤ) (by omega) ≫ H₁.map e.hom) :=
        congrArg (fun k => E.inv.app (F.obj M) ≫ k) hd
      _ = (E.inv.app (F.obj M) ≫ H.shiftMap q (0 : ℤ) (1 : ℤ) (by omega)) ≫
          H₁.map e.hom := (Category.assoc _ _ _).symm
      _ = (l ≫ K.homologyπ 1 ≫ P.inv) ≫ H₁.map e.hom :=
        congrArg (fun k => k ≫ H₁.map e.hom) hq
      _ = _ := by simp only [Category.assoc]
  have hv : A (F.rightDerivedSingleHomologyZeroIso.inv.app M s) =
      H₁.map e.hom (P.inv (K.homologyπ 1 (l s))) :=
    congrArg (fun k : F.obj M ⟶ H₁.obj (F.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj N)) => k s) hnorm
  have hExt : moduleResolutionSectionExtClass X α I 1 z =
      (Ext.mk₀ g).comp a (Nat.zero_add 1) := by
    have hc := resolutionSectionCocycle_precomp X α I f hf s
    change I.extEquivCohomologyClass.symm (.mk (moduleResolutionSectionCocycle X α I 1 z)) = _
    rw [I.extEquivCohomologyClass_symm_mk_precomp c g]
    exact congrArg I.extEquivCohomologyClass.symm (congrArg CohomologyClass.mk hc)
  calc
    _ = moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I 1
        (H₁.map e.hom (P.inv (K.homologyπ 1 (l s)))) :=
      congrArg (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I 1) hv
    _ = moduleResolutionSectionClass X α I 1 z :=
      moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_homologyπ X α I 1 (l s)
    _ = moduleExtCohomologyMap X N 1 (moduleResolutionSectionExtClass X α I 1 z) :=
      moduleResolutionSectionClass_apply X α I 1 z
    _ = _ := congrArg (moduleExtCohomologyMap X N 1) hExt

/-- The original degree-one Ext morphism acts on native derived sections
through its original Yoneda product with the actual degree-zero section. -/
theorem moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_extAction
    {M N : X.Modules} (I : InjectiveResolution N) (a : Ext.{u + 1} M N 1)
    (s : (moduleGlobalSectionsFunctorOfHom X α).obj M) :
    let := moduleCohomologyModuleOfHom X α N 1
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let g : O ⟶ M := (Scheme.Modules.unitHomGlobalSectionsEquiv X M).symm s
    moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I 1
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).shiftMap
        (a.homPlus.map (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus)
        (0 : ℤ) (1 : ℤ) (by omega)
        ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedSingleHomologyZeroIso.inv.app M s)) =
      moduleExtCohomologyMap X N 1 ((Ext.mk₀ g).comp a (Nat.zero_add 1)) := by
  obtain ⟨z, rfl⟩ := I.extEquivCohomologyClass.symm.surjective a
  obtain ⟨c, rfl⟩ := z.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective c 1 (zero_add (1 : ℤ)) 2 rfl
  exact derivedSections_extAction_fromSingle X α I f hf s

/-- The actual original boundary obtained by applying native derived global
sections to the original short-exact single triangle. -/
def moduleDerivedGlobalSectionsConnectingOfHom (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).obj
        ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj S.X₃)) ⟶
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 1).obj
        ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj S.X₁)) :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).homologySequenceδ
    ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.mapTriangle.obj
      hS.singleTrianglePlus) (0 : ℤ) (1 : ℤ) (by omega)

/-- The same original cohomology comparison preserves the actual native
degree-zero to degree-one boundary, with the original positive Ext sign. -/
theorem moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_connecting
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (I₁ : InjectiveResolution S.X₁) (I₃ : InjectiveResolution S.X₃)
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).obj
      ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj S.X₃))) :
    let := moduleCohomologyModuleOfHom X α S.X₁ 1
    let := moduleCohomologyModuleOfHom X α S.X₃ 0
    moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I₁ 1
        (moduleDerivedGlobalSectionsConnectingOfHom X α S hS x) =
      moduleCohomologyConnectingOfHom X α S hS 0
        (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I₃ 0 x) := by
  let := moduleCohomologyModuleOfHom X α S.X₁ 1
  let := moduleCohomologyModuleOfHom X α S.X₃ 0
  let F := moduleGlobalSectionsFunctorOfHom X α
  let E := F.rightDerivedSingleHomologyZeroIso.app S.X₃
  let s := E.hom x
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let g : O ⟶ S.X₃ := (Scheme.Modules.unitHomGlobalSectionsEquiv X S.X₃).symm s
  have hx : E.inv s = x := congrArg (fun k => k x) E.hom_inv_id
  have he₃ : moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I₃ 0 x =
      moduleExtCohomologyMap X S.X₃ 0 (Ext.mk₀ g) :=
    (congrArg (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I₃ 0) hx.symm).trans
      (moduleDerivedZeroClass X α S.X₃ I₃ s)
  have hδ : moduleDerivedGlobalSectionsConnectingOfHom X α S hS =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).shiftMap
        (hS.extClass.homPlus.map F.rightDerivedFunctorPlus) (0 : ℤ) (1 : ℤ) (by omega) := by
    rw [Ext.homPlus_extClass]
    rfl
  calc
    _ = moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I₁ 1
        (moduleDerivedGlobalSectionsConnectingOfHom X α S hS (E.inv s)) :=
      congrArg (fun y => moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I₁ 1
        (moduleDerivedGlobalSectionsConnectingOfHom X α S hS y)) hx.symm
    _ = moduleExtCohomologyMap X S.X₁ 1 ((Ext.mk₀ g).comp hS.extClass (Nat.zero_add 1)) := by
      rw [hδ]
      exact moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_extAction X α I₁ hS.extClass s
    _ = moduleCohomologyConnectingOfHom X α S hS 0
        (moduleExtCohomologyMap X S.X₃ 0 (Ext.mk₀ g)) :=
      moduleExtCohomologyMap_connectingOfHom X α S hS 0 (Ext.mk₀ g)
    _ = _ := congrArg (moduleCohomologyConnectingOfHom X α S hS 0) he₃.symm

end AlgebraicGeometry.Scheme.Cohomology
