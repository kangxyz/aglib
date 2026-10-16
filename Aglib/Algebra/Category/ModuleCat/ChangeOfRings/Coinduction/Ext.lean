/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Aglib.Algebra.Homology.ShortComplex.MapHomology.Components
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Homology of native derived coinduction and original Ext

The underlying additive cochain complex of the original scalar coinduction
is the native Hom complex from the restricted regular target ring. Its
component is the actual linear map, viewed as a cochain from degree zero.
The original forgetful homology comparison, native Hom-complex cohomology
classes and supplied injective resolution then identify its homology with
native Ext. This also computes homology of the installed D+ right-derived
functor at the original degree-zero single.

Both rings and module carriers have the same universe, as in the quotient
Ext consumer. Ext and the two supplied derived-category sizes remain
independent. The rings need not be commutative, and no flatness, regularity
or finiteness premise is used. The cycle and homology-projection formulas
retain the original cocycles. Target-ring scalar multiplication is exactly
native Yoneda precomposition with restricted right multiplication on the
regular target ring, also for the installed derived functor. Every original
coefficient map is native Yoneda postcomposition, and the higher-derived and
installed D+ comparisons are independent of the supplied resolution.
Quotient-linear transport and Koszul-class normalization are downstream consumers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open HomologicalComplex CochainComplex CochainComplex.HomComplex
noncomputable section
universe u w
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat
variable {R S : Type u} [Ring R] [Ring S] (σ : R →+* S)

/-- The original coinduced linear map is the actual cochain from the restricted target ring. -/
def coextendScalarsCochainEquiv (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (coextendScalars σ).obj (K.X n) ≃+
      Cochain ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        ((restrictScalars σ).obj (ModuleCat.of S S))) K n :=
  let e : (coextendScalars σ).obj (K.X n) ≃+
      (((restrictScalars σ).obj (ModuleCat.of S S)) ⟶ K.X n) :=
      {toFun := fun f => ModuleCat.ofHom
          (X := (restrictScalars σ).obj (ModuleCat.of S S)) (Y := K.X n)
          ((CoextendScalars.equiv σ (K.X n)) f)
       invFun := fun f => (CoextendScalars.equiv σ (K.X n)).symm f.hom
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl
       map_add' := fun _ _ => rfl}
  e.trans (Cochain.fromSingleEquiv (zero_add n)).symm

/-- The cochain comparison retains the original linear map on every component. -/
theorem coextendScalarsCochainEquiv_apply
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : (coextendScalars σ).obj (K.X n)) :
    coextendScalarsCochainEquiv σ K n x =
      Cochain.fromSingleMk
        (ModuleCat.ofHom (X := (restrictScalars σ).obj (ModuleCat.of S S)) (Y := K.X n)
          ((CoextendScalars.equiv σ (K.X n)) x)) (zero_add n) := rfl

/-- Underlying additive coinduction is the native Hom complex, with its original differential. -/
def coextendScalarsHomComplexIso (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (((coextendScalars σ) ⋙ forget₂ (ModuleCat S) AddCommGrpCat).mapHomologicalComplex
      (.up ℤ)).obj K ≅
      HomComplex ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        ((restrictScalars σ).obj (ModuleCat.of S S))) K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (coextendScalarsCochainEquiv σ K n).toAddCommGrpIso)
    (by
      intro i j hij
      ext x
      change δ i j (coextendScalarsCochainEquiv σ K i x) =
        coextendScalarsCochainEquiv σ K j ((coextendScalars σ).map (K.d i j) x)
      rw [coextendScalarsCochainEquiv_apply, Cochain.δ_fromSingleMk,
        coextendScalarsCochainEquiv_apply]
      rfl)

/-- Original coinduction cycles identify with native Hom-complex cocycles. -/
def coextendScalarsCyclesIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (forget₂ (ModuleCat S) AddCommGrpCat).obj
      ((((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj K).cycles n) ≅
      AddCommGrpCat.of (Cocycle ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        ((restrictScalars σ).obj (ModuleCat.of S S))) K n) :=
  (((((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj K).sc n).mapCyclesIso
      (forget₂ (ModuleCat S) AddCommGrpCat)).symm ≪≫
    asIso (HomologicalComplex.cyclesMap (coextendScalarsHomComplexIso σ K).hom n) ≪≫
    (HomComplex.leftHomologyData _ _ n).cyclesIso

/-- The cycle comparison retains the original linear map of each actual cycle. -/
theorem coextendScalarsCyclesIso_coe
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (z : (((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj K).cycles n) :
    ((coextendScalarsCyclesIso σ K n).hom z).1 =
      coextendScalarsCochainEquiv σ K n
        (((((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj K).iCycles n) z) := by
  let L := ((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj K
  let U := forget₂ (ModuleCat.{u} S) AddCommGrpCat
  let E := coextendScalarsHomComplexIso σ K
  let D := HomComplex.leftHomologyData
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((restrictScalars σ).obj (ModuleCat.of S S))) K n
  have hU : ((L.sc n).mapCyclesIso U).inv ≫
      ((L.sc n).map U).iCycles = U.map (L.sc n).iCycles := by
    exact ShortComplex.mapCyclesIso_inv_iCycles U (L.sc n)
  have h : (coextendScalarsCyclesIso σ K n).hom ≫ D.i =
      U.map (L.iCycles n) ≫ E.hom.f n := by
    dsimp only [coextendScalarsCyclesIso, Iso.trans_hom, Iso.symm_hom, asIso_hom]
    erw [Category.assoc, Category.assoc, D.cyclesIso_hom_comp_i,
      HomologicalComplex.cyclesMap_i, ← Category.assoc, hU]
    rfl
  exact ConcreteCategory.congr_hom h z

/-- Target-ring scalars act by the original restricted right-multiplication map. -/
theorem coextendScalarsCochainEquiv_smul
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (s : S)
    (x : (coextendScalars σ).obj (K.X n)) :
    coextendScalarsCochainEquiv σ K n (s • x) =
      Cochain.fromSingleMk
        ((restrictScalars σ).map
            (ModuleCat.ofHom (X := ModuleCat.of S S) (Y := ModuleCat.of S S)
              (LinearMap.mulRight S s)) ≫
          ModuleCat.ofHom
            (X := (restrictScalars σ).obj (ModuleCat.of S S)) (Y := K.X n)
            ((CoextendScalars.equiv σ (K.X n)) x)) (zero_add n) := by
  rw [coextendScalarsCochainEquiv_apply]
  congr 1

/-- The same original source multiplication computes the scalar action on actual cycles. -/
theorem coextendScalarsCyclesIso_smul
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (s : S)
    (z : (((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj K).cycles n) :
    (coextendScalarsCyclesIso σ K n).hom (s • z) =
      ((coextendScalarsCyclesIso σ K n).hom z).precomp
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map
          ((restrictScalars σ).map
            (ModuleCat.ofHom (X := ModuleCat.of S S) (Y := ModuleCat.of S S)
              (LinearMap.mulRight S s)))) := by
  apply Subtype.ext
  change ((coextendScalarsCyclesIso σ K n).hom (s • z)).1 =
    (Cochain.ofHom ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map
      ((restrictScalars σ).map
        (ModuleCat.ofHom (X := ModuleCat.of S S) (Y := ModuleCat.of S S)
          (LinearMap.mulRight S s))))).comp
      ((coextendScalarsCyclesIso σ K n).hom z).1 (zero_add n)
  rw [coextendScalarsCyclesIso_coe, map_smul,
    coextendScalarsCochainEquiv_smul, coextendScalarsCyclesIso_coe,
    coextendScalarsCochainEquiv_apply, ← Cochain.fromSingleMk_precomp]

private theorem coextendScalars_homologyπ_components
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    let L := ((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj K
    let U := forget₂ (ModuleCat.{u} S) AddCommGrpCat
    let E := coextendScalarsHomComplexIso σ K
    let D := HomComplex.leftHomologyData
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        ((restrictScalars σ).obj (ModuleCat.of S S))) K n
    U.map (L.homologyπ n) ≫ ((L.sc n).mapHomologyIso U).inv ≫
      HomologicalComplex.homologyMap E.hom n ≫ D.homologyIso.hom =
        (coextendScalarsCyclesIso σ K n).hom ≫ D.π := by
  dsimp only
  let L := ((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj K
  let U := forget₂ (ModuleCat.{u} S) AddCommGrpCat
  let E := coextendScalarsHomComplexIso σ K
  let C := HomComplex
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((restrictScalars σ).obj (ModuleCat.of S S))) K
  let D := HomComplex.leftHomologyData
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((restrictScalars σ).obj (ModuleCat.of S S))) K n
  let T : ShortComplex AddCommGrpCat := (L.sc n).map U
  let P : T ⟶ C.sc n :=
    (HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map E.hom
  have hP : T.homologyπ ≫ ShortComplex.homologyMap P ≫ D.homologyIso.hom =
      ShortComplex.cyclesMap P ≫ D.cyclesIso.hom ≫ D.π := by
    rw [ShortComplex.homologyπ_naturality_assoc]
    erw [D.homologyπ_comp_homologyIso_hom]
  change U.map (L.homologyπ n) ≫ ((L.sc n).mapHomologyIso U).inv ≫
    ShortComplex.homologyMap P ≫ D.homologyIso.hom = _
  erw [ShortComplex.map_homologyπ_mapHomologyIso_inv_assoc]
  rw [hP]
  simp only [coextendScalarsCyclesIso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, HomologicalComplex.cyclesMap, Category.assoc]
  rfl


private theorem coextendScalars_homologyπ_class
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (z : (((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj K).cycles n) :
    (HomComplex.homologyAddEquiv
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        ((restrictScalars σ).obj (ModuleCat.of S S))) K n)
      (HomologicalComplex.homologyMap (coextendScalarsHomComplexIso σ K).hom n
        ((((((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj K).sc n).mapHomologyIso
          (forget₂ (ModuleCat S) AddCommGrpCat)).inv
            (((((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj K).homologyπ n) z))) =
      CohomologyClass.mk ((coextendScalarsCyclesIso σ K n).hom z) := by
  let L := ((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj K
  let A := AddCommGrpCat.of
    (CohomologyClass ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((restrictScalars σ).obj (ModuleCat.of S S))) K n)
  exact congrArg (fun f : (forget₂ (ModuleCat S) AddCommGrpCat).obj (L.cycles n) ⟶ A =>
    f.hom z) (coextendScalars_homologyπ_components σ K n)

/-- Original coefficient cochain maps give literal postcomposition of the original cocycles. -/
theorem coextendScalarsCyclesIso_postcomp
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (n : ℤ)
    (z : (((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj K).cycles n) :
    (coextendScalarsCyclesIso σ L n).hom
        (cyclesMap (((coextendScalars σ).mapHomologicalComplex (.up ℤ)).map f) n z) =
      ((coextendScalarsCyclesIso σ K n).hom z).postcomp f := by
  let Kσ := ((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj K
  let Lσ := ((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj L
  let fσ := ((coextendScalars σ).mapHomologicalComplex (.up ℤ)).map f
  have hi : Lσ.iCycles n (cyclesMap fσ n z) =
      (coextendScalars σ).map (f.f n) (Kσ.iCycles n z) := by
    exact congrArg (fun h : Kσ.cycles n ⟶ Lσ.X n => h.hom z) (cyclesMap_i fσ n)
  apply Subtype.ext
  change ((coextendScalarsCyclesIso σ L n).hom (cyclesMap fσ n z)).1 =
    ((coextendScalarsCyclesIso σ K n).hom z).1.comp (Cochain.ofHom f) (add_zero n)
  rw [coextendScalarsCyclesIso_coe, coextendScalarsCyclesIso_coe, hi,
    coextendScalarsCochainEquiv_apply, coextendScalarsCochainEquiv_apply,
    ← Cochain.fromSingleMk_postcomp]
  rfl

variable [HasExt.{w} (ModuleCat.{u} R)]

/-- The supplied original injective resolution computes coinduction homology
as native Ext. -/
def coextendScalarsResolutionExtAddEquiv {M : ModuleCat.{u} R}
    (I : InjectiveResolution M) (n : ℕ) :
    (((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homology
      (n : ℤ) ≃+
      Ext.{w} ((restrictScalars σ).obj (ModuleCat.of S S)) M n := by
  let K := ((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let U := forget₂ (ModuleCat.{u} S) AddCommGrpCat
  let e₁ : U.obj (K.homology (n : ℤ)) ≅
      ((U.mapHomologicalComplex (.up ℤ)).obj K).homology (n : ℤ) :=
    ((K.sc (n : ℤ)).mapHomologyIso U).symm
  let e₂ := (homologyFunctor AddCommGrpCat (.up ℤ) (n : ℤ)).mapIso
    (coextendScalarsHomComplexIso σ I.cochainComplex)
  exact e₁.addCommGroupIsoToAddEquiv.trans
    (e₂.addCommGroupIsoToAddEquiv.trans
      ((HomComplex.homologyAddEquiv _ _ (n : ℤ)).trans
        I.extAddEquivCohomologyClass.symm))

/-- The Ext comparison retains its original forgetful, Hom-complex and cocycle factors. -/
theorem coextendScalarsResolutionExtAddEquiv_apply {M : ModuleCat.{u} R}
    (I : InjectiveResolution M) (n : ℕ)
    (x : (((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj
      I.cochainComplex).homology (n : ℤ)) :
    coextendScalarsResolutionExtAddEquiv σ I n x =
      I.extAddEquivCohomologyClass.symm
        ((HomComplex.homologyAddEquiv
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
            ((restrictScalars σ).obj (ModuleCat.of S S))) I.cochainComplex (n : ℤ))
          (HomologicalComplex.homologyMap (coextendScalarsHomComplexIso σ I.cochainComplex).hom
            (n : ℤ)
            ((((((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj
              I.cochainComplex).sc (n : ℤ)).mapHomologyIso
                (forget₂ (ModuleCat S) AddCommGrpCat)).inv x))) := rfl

/-- Projecting an actual cycle gives its unchanged native injective-resolution Ext class. -/
theorem coextendScalarsResolutionExtAddEquiv_homologyπ {M : ModuleCat.{u} R}
    (I : InjectiveResolution M) (n : ℕ)
    (z : (((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj
      I.cochainComplex).cycles (n : ℤ)) :
    coextendScalarsResolutionExtAddEquiv σ I n
        (((((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex).homologyπ (n : ℤ)) z) =
      I.extAddEquivCohomologyClass.symm
        (CohomologyClass.mk ((coextendScalarsCyclesIso σ I.cochainComplex (n : ℤ)).hom z)) := by
  rw [coextendScalarsResolutionExtAddEquiv_apply,
    coextendScalars_homologyπ_class σ I.cochainComplex (n : ℤ) z]

/-- Target-ring scalars on original resolution homology are native Yoneda source multiplication. -/
theorem coextendScalarsResolutionExtAddEquiv_smul {M : ModuleCat.{u} R}
    (I : InjectiveResolution M) (n : ℕ) (s : S)
    (x : (((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj
      I.cochainComplex).homology (n : ℤ)) :
    coextendScalarsResolutionExtAddEquiv σ I n (s • x) =
      (Ext.mk₀ ((restrictScalars σ).map
        (ModuleCat.ofHom (X := ModuleCat.of S S) (Y := ModuleCat.of S S)
          (LinearMap.mulRight S s)))).comp
        (coextendScalarsResolutionExtAddEquiv σ I n x) (zero_add n) := by
  let A : ModuleCat.{u} R := (restrictScalars σ).obj (ModuleCat.of S S)
  let L := ((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let E := coextendScalarsResolutionExtAddEquiv σ I n
  let C := coextendScalarsCyclesIso σ I.cochainComplex (n : ℤ)
  let g : A ⟶ A := (restrictScalars σ).map
    (ModuleCat.ofHom (X := ModuleCat.of S S) (Y := ModuleCat.of S S)
      (LinearMap.mulRight S s))
  obtain ⟨f, hf, hfx⟩ := I.extMk_surjective (E x) (n + 1) rfl
  let c : Cocycle ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj A)
      I.cochainComplex (n : ℤ) :=
    Cocycle.fromSingleMk (f ≫ (I.cochainComplexXIso n n rfl).inv)
      (zero_add _) ((n + 1 : ℕ) : ℤ) (by lia)
      (by
        erw [I.cochainComplex_d (n : ℤ) ((n + 1 : ℕ) : ℤ) n (n + 1) rfl rfl]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hf, zero_comp])
  let z : L.cycles (n : ℤ) := C.inv c
  have hc : C.hom z = c := by
    exact Iso.inv_hom_id_apply C c
  have hz : E (L.homologyπ (n : ℤ) z) = I.extMk f (n + 1) rfl hf := by
    rw [coextendScalarsResolutionExtAddEquiv_homologyπ, hc]
    rfl
  have hzx : L.homologyπ (n : ℤ) z = x := E.injective (hz.trans hfx)
  have hcs : C.hom (s • z) = c.precomp
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map g) := by
    rw [coextendScalarsCyclesIso_smul, hc]
  have hclass : I.extAddEquivCohomologyClass.symm
      (CohomologyClass.mk (c.precomp
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map g))) =
      (Ext.mk₀ g).comp (I.extMk f (n + 1) rfl hf) (zero_add n) := by
    rw [I.mk₀_comp_extMk]
    change I.extEquivCohomologyClass.symm _ = _
    apply I.extEquivCohomologyClass.injective
    simp only [Equiv.apply_symm_apply, I.extEquivCohomologyClass_extMk]
    apply congrArg CohomologyClass.mk
    dsimp only [c]
    rw [← Cocycle.fromSingleMk_precomp]
    simp only [Category.assoc]
  rw [← hzx, ← map_smul, coextendScalarsResolutionExtAddEquiv_homologyπ, hcs]
  exact hclass.trans (congrArg (fun e => (Ext.mk₀ g).comp e (zero_add n)) hz.symm)

/-- Every original coefficient-resolution lift retains native Yoneda postcomposition. -/
theorem coextendScalarsResolutionExtAddEquiv_naturality
    {M N : ModuleCat.{u} R} {I : InjectiveResolution M} {J : InjectiveResolution N}
    {g : M ⟶ N} (φ : InjectiveResolution.Hom I J g) (n : ℕ)
    (x : (((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj
      I.cochainComplex).homology (n : ℤ)) :
    coextendScalarsResolutionExtAddEquiv σ J n
        (homologyMap (((coextendScalars σ).mapHomologicalComplex (.up ℤ)).map φ.hom')
          (n : ℤ) x) =
      (coextendScalarsResolutionExtAddEquiv σ I n x).comp (Ext.mk₀ g) (add_zero n) := by
  let A : ModuleCat.{u} R := (restrictScalars σ).obj (ModuleCat.of S S)
  let L := ((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let L' := ((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let fφ := ((coextendScalars σ).mapHomologicalComplex (.up ℤ)).map φ.hom'
  let E := coextendScalarsResolutionExtAddEquiv σ I n
  let C := coextendScalarsCyclesIso σ I.cochainComplex (n : ℤ)
  obtain ⟨f, hf, hfx⟩ := I.extMk_surjective (E x) (n + 1) rfl
  let c : Cocycle ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj A)
      I.cochainComplex (n : ℤ) :=
    Cocycle.fromSingleMk (f ≫ (I.cochainComplexXIso n n rfl).inv)
      (zero_add _) ((n + 1 : ℕ) : ℤ) (by lia)
      (by
        erw [I.cochainComplex_d (n : ℤ) ((n + 1 : ℕ) : ℤ) n (n + 1) rfl rfl]
        simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hf, zero_comp])
  let z : L.cycles (n : ℤ) := C.inv c
  have hc : C.hom z = c := by
    exact Iso.inv_hom_id_apply C c
  have hz : E (L.homologyπ (n : ℤ) z) = I.extMk f (n + 1) rfl hf := by
    rw [coextendScalarsResolutionExtAddEquiv_homologyπ, hc]
    rfl
  have hzx : L.homologyπ (n : ℤ) z = x := E.injective (hz.trans hfx)
  have hmap : homologyMap fφ (n : ℤ) (L.homologyπ (n : ℤ) z) =
      L'.homologyπ (n : ℤ) (cyclesMap fφ (n : ℤ) z) := by
    exact congrArg (fun h : L.cycles (n : ℤ) ⟶ L'.homology (n : ℤ) => h.hom z)
      (homologyπ_naturality fφ (n : ℤ))
  have hclass : J.extAddEquivCohomologyClass.symm (CohomologyClass.mk (c.postcomp φ.hom')) =
      (I.extMk f (n + 1) rfl hf).comp (Ext.mk₀ g) (add_zero n) := by
    rw [I.extMk_comp_mk₀ f (n + 1) rfl hf φ]
    change J.extEquivCohomologyClass.symm _ = _
    apply J.extEquivCohomologyClass.injective
    simp only [Equiv.apply_symm_apply, J.extEquivCohomologyClass_extMk]
    apply congrArg CohomologyClass.mk
    dsimp only [c]
    rw [← Cocycle.fromSingleMk_postcomp]
    congr 1
    simp [φ.hom'_f n n rfl]
  rw [← hzx, hmap, coextendScalarsResolutionExtAddEquiv_homologyπ,
    coextendScalarsCyclesIso_postcomp, hc]
  exact hclass.trans (congrArg (fun e => e.comp (Ext.mk₀ g) (add_zero n)) hz.symm)

/-- Native higher right-derived coinduction has the original Ext group
as its additive carrier. -/
def coextendScalarsRightDerivedExtAddEquiv (M : ModuleCat.{u} R)
    (I : InjectiveResolution M) (n : ℕ) :
    ((coextendScalars σ).rightDerived n).obj M ≃+
      Ext.{w} ((restrictScalars σ).obj (ModuleCat.of S S)) M n :=
  (I.isoRightDerivedObjCochain (coextendScalars σ) n).toLinearEquiv.toAddEquiv.trans
    (coextendScalarsResolutionExtAddEquiv σ I n)

/-- The native higher-derived comparison retains the same original target-ring scalar action. -/
theorem coextendScalarsRightDerivedExtAddEquiv_smul
    (M : ModuleCat.{u} R) (I : InjectiveResolution M) (n : ℕ) (s : S)
    (x : ((coextendScalars σ).rightDerived n).obj M) :
    coextendScalarsRightDerivedExtAddEquiv σ M I n (s • x) =
      (Ext.mk₀ ((restrictScalars σ).map
        (ModuleCat.ofHom (X := ModuleCat.of S S) (Y := ModuleCat.of S S)
          (LinearMap.mulRight S s)))).comp
        (coextendScalarsRightDerivedExtAddEquiv σ M I n x) (zero_add n) := by
  change coextendScalarsResolutionExtAddEquiv σ I n
      ((I.isoRightDerivedObjCochain (coextendScalars σ) n).toLinearEquiv (s • x)) =
    (Ext.mk₀ ((restrictScalars σ).map
      (ModuleCat.ofHom (X := ModuleCat.of S S) (Y := ModuleCat.of S S)
        (LinearMap.mulRight S s)))).comp
      (coextendScalarsResolutionExtAddEquiv σ I n
        ((I.isoRightDerivedObjCochain (coextendScalars σ) n).toLinearEquiv x)) (zero_add n)
  rw [map_smul, coextendScalarsResolutionExtAddEquiv_smul]

/-- The original higher-derived coefficient map is native Yoneda coefficient postcomposition. -/
theorem coextendScalarsRightDerivedExtAddEquiv_naturality
    {M N : ModuleCat.{u} R} (I : InjectiveResolution M) (J : InjectiveResolution N)
    (g : M ⟶ N) (n : ℕ) (x : ((coextendScalars σ).rightDerived n).obj M) :
    coextendScalarsRightDerivedExtAddEquiv σ N J n
        (((coextendScalars σ).rightDerived n).map g x) =
      (coextendScalarsRightDerivedExtAddEquiv σ M I n x).comp (Ext.mk₀ g) (add_zero n) := by
  let φ : InjectiveResolution.Hom I J g :=
    ⟨InjectiveResolution.desc g J I, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero g J I⟩
  let eI := I.isoRightDerivedObjCochain (coextendScalars σ) n
  let eJ := J.isoRightDerivedObjCochain (coextendScalars σ) n
  have h : eJ.hom (((coextendScalars σ).rightDerived n).map g x) =
      homologyMap (((coextendScalars σ).mapHomologicalComplex (.up ℤ)).map φ.hom')
        (n : ℤ) (eI.hom x) := by
    exact congrArg (fun h : ((coextendScalars σ).rightDerived n).obj M ⟶
      (((coextendScalars σ).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex).homology
        (n : ℤ) => h.hom x)
      (InjectiveResolution.isoRightDerivedObjCochain_hom_naturality (coextendScalars σ) φ n)
  change coextendScalarsResolutionExtAddEquiv σ J n
      (eJ.hom (((coextendScalars σ).rightDerived n).map g x)) =
    (coextendScalarsResolutionExtAddEquiv σ I n (eI.hom x)).comp (Ext.mk₀ g) (add_zero n)
  rw [h, coextendScalarsResolutionExtAddEquiv_naturality]

/-- The unchanged higher-derived Ext comparison is independent of the supplied resolution. -/
theorem coextendScalarsRightDerivedExtAddEquiv_independent
    (M : ModuleCat.{u} R) (I J : InjectiveResolution M) (n : ℕ) :
    coextendScalarsRightDerivedExtAddEquiv σ M I n =
      coextendScalarsRightDerivedExtAddEquiv σ M J n := by
  apply AddEquiv.ext
  intro x
  have h := coextendScalarsRightDerivedExtAddEquiv_naturality σ I J (𝟙 M) n x
  simpa using h.symm

universe a b
variable [HasDerivedCategory.{a} (ModuleCat.{u} R)]
  [HasDerivedCategory.{b} (ModuleCat.{u} S)]

/-- Homology of the installed D+ coinduction at the original single computes the same native Ext. -/
def derivedCoextendScalarsPlusHomologyExtAddEquiv (M : ModuleCat.{u} R)
    (I : InjectiveResolution M) (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
      ((coextendScalars σ).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj M)) ≃+
      Ext.{w} ((restrictScalars σ).obj (ModuleCat.of S S)) M n :=
  (I.isoRightDerivedSingleHomology (coextendScalars σ) n).symm.toLinearEquiv.toAddEquiv.trans
      (coextendScalarsRightDerivedExtAddEquiv σ M I n)

/-- The installed D+ comparison retains target scalars as original Yoneda precomposition. -/
theorem derivedCoextendScalarsPlusHomologyExtAddEquiv_smul
    (M : ModuleCat.{u} R) (I : InjectiveResolution M) (n : ℕ) (s : S)
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
      ((coextendScalars σ).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj M))) :
    derivedCoextendScalarsPlusHomologyExtAddEquiv σ M I n (s • x) =
      (Ext.mk₀ ((restrictScalars σ).map
        (ModuleCat.ofHom (X := ModuleCat.of S S) (Y := ModuleCat.of S S)
          (LinearMap.mulRight S s)))).comp
        (derivedCoextendScalarsPlusHomologyExtAddEquiv σ M I n x) (zero_add n) := by
  change coextendScalarsRightDerivedExtAddEquiv σ M I n
      ((I.isoRightDerivedSingleHomology (coextendScalars σ) n).symm.toLinearEquiv (s • x)) =
    (Ext.mk₀ ((restrictScalars σ).map
      (ModuleCat.ofHom (X := ModuleCat.of S S) (Y := ModuleCat.of S S)
        (LinearMap.mulRight S s)))).comp
      (coextendScalarsRightDerivedExtAddEquiv σ M I n
        ((I.isoRightDerivedSingleHomology (coextendScalars σ) n).symm.toLinearEquiv x))
      (zero_add n)
  rw [map_smul, coextendScalarsRightDerivedExtAddEquiv_smul]

/-- The actual installed derived coefficient map is original Yoneda postcomposition. -/
theorem derivedCoextendScalarsPlusHomologyExtAddEquiv_naturality
    {M N : ModuleCat.{u} R} (I : InjectiveResolution M) (J : InjectiveResolution N)
    (g : M ⟶ N) (n : ℕ)
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
      ((coextendScalars σ).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj M))) :
    derivedCoextendScalarsPlusHomologyExtAddEquiv σ N J n
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).map
          ((coextendScalars σ).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map g)) x) =
      (derivedCoextendScalarsPlusHomologyExtAddEquiv σ M I n x).comp
        (Ext.mk₀ g) (add_zero n) := by
  let φ : InjectiveResolution.Hom I J g :=
    ⟨InjectiveResolution.desc g J I, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero g J I⟩
  let eI := I.isoRightDerivedSingleHomology (coextendScalars σ) n
  let eJ := J.isoRightDerivedSingleHomology (coextendScalars σ) n
  let d := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).map
    ((coextendScalars σ).rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).map g))
  have he : ((coextendScalars σ).rightDerived n).map g ≫ eJ.hom = eI.hom ≫ d :=
    InjectiveResolution.isoRightDerivedSingleHomology_hom_naturality (coextendScalars σ) φ n
  have hh : d ≫ eJ.inv = eI.inv ≫ ((coextendScalars σ).rightDerived n).map g := by
    apply (cancel_mono eJ.hom).mp
    rw [Category.assoc, eJ.inv_hom_id, Category.comp_id, Category.assoc, he,
      ← Category.assoc, eI.inv_hom_id, Category.id_comp]
  have h : eJ.inv (d x) = ((coextendScalars σ).rightDerived n).map g (eI.inv x) := by
    exact congrArg (fun h : (DerivedCategory.Plus.homologyFunctor
      (ModuleCat.{u} S) (n : ℤ)).obj
        ((coextendScalars σ).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj M)) ⟶
      ((coextendScalars σ).rightDerived n).obj N => h.hom x) hh
  change coextendScalarsRightDerivedExtAddEquiv σ N J n (eJ.inv (d x)) =
    (coextendScalarsRightDerivedExtAddEquiv σ M I n (eI.inv x)).comp (Ext.mk₀ g) (add_zero n)
  rw [h, coextendScalarsRightDerivedExtAddEquiv_naturality]

/-- The installed derived homology comparison is independent of the supplied resolution. -/
theorem derivedCoextendScalarsPlusHomologyExtAddEquiv_independent
    (M : ModuleCat.{u} R) (I J : InjectiveResolution M) (n : ℕ) :
    derivedCoextendScalarsPlusHomologyExtAddEquiv σ M I n =
      derivedCoextendScalarsPlusHomologyExtAddEquiv σ M J n := by
  apply AddEquiv.ext
  intro x
  have h := derivedCoextendScalarsPlusHomologyExtAddEquiv_naturality σ I J (𝟙 M) n x
  simpa using h.symm

end ModuleCat
