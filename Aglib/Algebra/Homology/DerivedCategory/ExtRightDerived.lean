/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Embedding.MapExtend.Naturality
public import Aglib.CategoryTheory.Abelian.RightDerived.Cochain
public import Aglib.CategoryTheory.Abelian.Injective.ExtZero
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Original Ext and the right-derived additive Hom functor

The supplied injective resolution computes the original Ext group and the
original natural-degree right-derived additive Hom functor. The Ext universe
is independent of the morphism universe. The comparison uses the native
`extAddEquivCohomologyClass`, hence the original augmentation `ι'`, rather than
a second extension or localization construction.

Reconciled from `Motivic/Aglib/Algebra/Homology/DerivedCategory/ExtRightDerived.lean`
and the private Hom-complex comparisons from
`HomotopyCategory/HomComplexSingleIso.lean` and `HomComplexNaturality.lean`
at Motivic revision `57e94dc5db72b38129032ed2d39a2fd5117e9f9e`.
The extension and resolution-homology comparisons are the native Aglib providers.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex

universe w v u

namespace CochainComplex.HomComplex.ExtRightDerived
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K K' L L' : CochainComplex C ℤ} (f : K' ⟶ K) (g : L ⟶ L')

/-- The genuine contravariant/covariant map of Hom complexes. -/
private def map : HomComplex K L ⟶ HomComplex K' L' where
  f n := AddCommGrpCat.ofHom
    { toFun := fun α => ((Cochain.ofHom f).comp α (zero_add n)).comp
        (Cochain.ofHom g) (add_zero n)
      map_zero' := by simp
      map_add' := by intros; simp }
  comm' i j _ := by ext α; simp

/-- The induced map on cocycles, without choosing representatives of cohomology classes. -/
private def cocycleMap (n : ℤ) : Cocycle K L n →+ Cocycle K' L' n where
  toFun α := (α.precomp f).postcomp g
  map_zero' := by ext; simp [Cocycle.precomp, Cocycle.postcomp]
  map_add' := by intros; ext; simp [Cocycle.precomp, Cocycle.postcomp]

/-- The cohomology-class map is characterized by composition in the actual homotopy category. -/
private def classMap (n : ℤ) : CohomologyClass K L n →+ CohomologyClass K' L' n where
  toFun x := CohomologyClass.homAddEquiv.symm
    ((HomotopyCategory.quotient C _).map f ≫ CohomologyClass.toHom x ≫
      (HomotopyCategory.quotient C _).map (g⟦n⟧'))
  map_zero' := by simp
  map_add' := by intros; simp

@[simp]
private theorem classMap_mk (n : ℤ) (z : Cocycle K L n) :
    classMap f g n (CohomologyClass.mk z) =
      CohomologyClass.mk ((z.precomp f).postcomp g) := by
  apply CohomologyClass.homAddEquiv.injective
  simp [classMap, CohomologyClass.homAddEquiv, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_precomp, Cocycle.equivHomShift_symm_postcomp,
    Functor.map_comp]

/-- The quotient cocycle construction computes the genuine map on homology. -/
private def mapLeftHomologyData (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor _ _ n).map (map f g))
      (leftHomologyData K L n) (leftHomologyData K' L' n) where
  φK := AddCommGrpCat.ofHom (cocycleMap f g n)
  φH := AddCommGrpCat.ofHom (classMap f g n)
  commi := by ext z; rfl
  commf' := by
    apply (cancel_mono (leftHomologyData K' L' n).i).1
    have hi : AddCommGrpCat.ofHom (cocycleMap f g n) ≫ (leftHomologyData K' L' n).i =
        (leftHomologyData K L n).i ≫ (map f g).f n := by ext z; rfl
    rw [Category.assoc, hi, ← Category.assoc, ShortComplex.LeftHomologyData.f'_i,
      Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((HomologicalComplex.shortComplexFunctor _ _ n).map (map f g)).comm₁₂.symm
  commπ := by ext z; exact classMap_mk f g n z

/-- Hom-complex homology and cohomology classes have the same actual functorial maps. -/
private theorem homologyAddEquiv_naturality (n : ℤ) (x : (HomComplex K L).homology n) :
    homologyAddEquiv K' L' n (HomologicalComplex.homologyMap (map f g) n x) =
      classMap f g n (homologyAddEquiv K L n x) :=
  ConcreteCategory.congr_hom (mapLeftHomologyData f g n).homologyMap_comm x

end CochainComplex.HomComplex.ExtRightDerived


namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- Evaluate the original single-source Hom complex in degree zero. The
evaluation retains the supplied single-object component isomorphism. -/
def homComplexSingleIso (X : C) (K : CochainComplex C ℤ) :
    CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj X) K ≅
      ((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex _).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (CochainComplex.HomComplex.Cochain.fromSingleEquiv (X := X) (K := K)
      (show (0 : ℤ) + n = n by simp)).toAddCommGrpIso)
    (by
      intro i j hij
      ext α
      obtain ⟨f, rfl⟩ :=
        CochainComplex.HomComplex.Cochain.fromSingleMk_surjective α i (by simp)
      symm
      simpa using congrArg
        (CochainComplex.HomComplex.Cochain.fromSingleEquiv (X := X) (K := K)
          (show (0 : ℤ) + j = j by simp))
        (CochainComplex.HomComplex.Cochain.δ_fromSingleMk f
          (show (0 : ℤ) + i = i by simp) j j (by simp)))

open CochainComplex

/-- Evaluation at the original object respects actual source and coefficient maps. -/
@[reassoc]
private theorem homComplexSingleIso_naturality {X X' : C} (f : X' ⟶ X)
    {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    HomComplex.ExtRightDerived.map ((singleFunctor C 0).map f) g ≫ (homComplexSingleIso X' L).hom =
      (homComplexSingleIso X K).hom ≫
        (NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map f.op) _).app K ≫
        ((preadditiveCoyoneda.obj (Opposite.op X')).mapHomologicalComplex _).map g := by
  ext n α
  obtain ⟨h, rfl⟩ := HomComplex.Cochain.fromSingleMk_surjective α n (by simp)
  change HomComplex.Cochain.fromSingleEquiv (show (0 : ℤ) + n = n by simp)
      (((HomComplex.Cochain.ofHom ((singleFunctor C 0).map f)).comp
        (HomComplex.Cochain.fromSingleMk h (show (0 : ℤ) + n = n by simp)) (zero_add n)).comp
        (HomComplex.Cochain.ofHom g) (add_zero n)) = _
  rw [← HomComplex.Cochain.fromSingleMk_precomp, ← HomComplex.Cochain.fromSingleMk_postcomp]
  simp only [homComplexSingleIso, HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
  simp only [Category.assoc, HomComplex_X, preadditiveCoyoneda_obj,
    Functor.mapHomologicalComplex_obj_X, Functor.comp_obj, ModuleCat.forget₂_obj,
    preadditiveCoyonedaObj_obj_carrier, HomologicalComplex.comp_f,
    HomologicalComplex.Hom.isoOfComponents_hom_f, AddEquiv.toAddCommGrpIso_hom,
    AddEquiv.toAddMonoidHom_eq_coe, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, Functor.comp_map, preadditiveCoyonedaObj_map,
    ModuleCat.forget₂_map, ConcreteCategory.hom_ofHom, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, LinearMap.coe_mk, AddHom.coe_mk,
    Function.comp_apply, HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
  change f ≫ h ≫ g.f n = (f ≫ h) ≫ g.f n
  exact (Category.assoc _ _ _).symm


end CochainComplex

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]

omit [Abelian C] in
private theorem iso_comparison_naturality
    {A₀ A₁ B₀ B₁ D₀ D₁ : C}
    (E₀ : A₀ ≅ B₀) (E₁ : A₁ ≅ B₁) (C₀ : D₀ ≅ B₀) (C₁ : D₁ ≅ B₁)
    (f : A₀ ⟶ A₁) (h : B₀ ⟶ B₁) (g : D₀ ⟶ D₁)
    (hE : f ≫ E₁.hom = E₀.hom ≫ h) (hC : g ≫ C₁.hom = C₀.hom ≫ h) :
    f ≫ (E₁ ≪≫ C₁.symm).hom = (E₀ ≪≫ C₀.symm).hom ≫ g := by
  apply (cancel_mono C₁.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [hC]
  simp only [Iso.inv_hom_id_assoc]
  exact hE

open CochainComplex

/-- Evaluation of a single-source Hom cocycle preserves its actual homology class. -/
private theorem homology_homComplexSingleIso_fromSingleMk
    (X : C) (K : CochainComplex C ℤ) (n : ℤ) (f : X ⟶ K.X n)
    (hf : f ≫ K.d n (n + 1) = 0) :
    homologyMap (homComplexSingleIso X K).hom n
        ((HomComplex.homologyAddEquiv _ _ n).symm
          (.mk (HomComplex.Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf))) =
      let H := ((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex (.up ℤ)).obj K
      H.homologyπ n ((H.sc n).abCyclesIso.inv ⟨f, by
        change f ≫ K.d n ((ComplexShape.up ℤ).next n) = 0
        rw [CochainComplex.next ℤ n]
        exact hf⟩) := by
  let L := HomComplex ((singleFunctor C 0).obj X) K
  let H := ((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex (.up ℤ)).obj K
  let E := homComplexSingleIso X K
  let z := HomComplex.Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf
  let d := HomComplex.leftHomologyData ((singleFunctor C 0).obj X) K n
  have hπ : (HomComplex.homologyAddEquiv _ _ n).symm (.mk z) =
      L.homologyπ n (d.cyclesIso.inv z) :=
    ConcreteCategory.congr_hom d.π_comp_homologyIso_inv z
  have hi : L.iCycles n (d.cyclesIso.inv z) = z.1 :=
    ConcreteCategory.congr_hom d.cyclesIso_inv_comp_iCycles z
  have hc : cyclesMap E.hom n (d.cyclesIso.inv z) =
      (H.sc n).abCyclesIso.inv ⟨f, by
        change f ≫ K.d n ((ComplexShape.up ℤ).next n) = 0
        rw [CochainComplex.next ℤ n]
        exact hf⟩ := by
    apply (AddCommGrpCat.mono_iff_injective (H.iCycles n)).mp inferInstance
    rw [← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply, hi]
    erw [HomologicalComplex.iCycles, ShortComplex.abCyclesIso_inv_apply_iCycles]
    exact HomComplex.Cochain.fromSingleEquiv_fromSingleMk f (zero_add n)
  change homologyMap E.hom n ((HomComplex.homologyAddEquiv _ _ n).symm (.mk z)) = _
  rw [hπ, ← ConcreteCategory.comp_apply, homologyπ_naturality,
    ConcreteCategory.comp_apply, hc]

variable [EnoughInjectives C] {Y : C} (I : InjectiveResolution Y) (X : C) (n : ℕ)

/-- Evaluation of the actual Hom complex followed by the inverse native integer
resolution comparison computes the original right-derived additive Hom functor. -/
def homComplexHomologyRightDerivedIso :
    (CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj X)
      I.cochainComplex).homology (n : ℤ) ≅
      ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).obj Y :=
  (homologyFunctor _ _ (n : ℤ)).mapIso (homComplexSingleIso X I.cochainComplex) ≪≫
    (I.isoRightDerivedObjCochain (preadditiveCoyoneda.obj (Opposite.op X)) n).symm

variable [HasExt.{w} C]

/-- Original Ext, in any declared Ext universe, computes the actual right-derived
additive Hom functor through the supplied original injective resolution. -/
def extRightDerivedAddEquiv : Abelian.Ext.{w} X Y n ≃+
    ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).obj Y :=
  I.extAddEquivCohomologyClass.trans
    ((CochainComplex.HomComplex.homologyAddEquiv _ _ (n : ℤ)).symm.trans
      (I.homComplexHomologyRightDerivedIso X n).addCommGroupIsoToAddEquiv)

/-- The comparison retains the actual cohomology class of the original resolution,
not merely an abstract isomorphism between the resulting additive groups. -/
theorem extRightDerivedAddEquiv_apply (x : Abelian.Ext.{w} X Y n) :
    I.extRightDerivedAddEquiv X n x =
      (I.homComplexHomologyRightDerivedIso X n).hom
        ((CochainComplex.HomComplex.homologyAddEquiv _ _ (n : ℤ)).symm
          (I.extAddEquivCohomologyClass x)) := rfl

/-- Every original resolution cocycle is sent through the same Hom-complex homology
comparison. This fixes the representative-level normalization of the equivalence. -/
theorem extRightDerivedAddEquiv_extMk
    (f : X ⟶ I.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ I.cocomplex.d n m = 0) :
    I.extRightDerivedAddEquiv X n (I.extMk f m hm hf) =
      (I.homComplexHomologyRightDerivedIso X n).hom
        ((CochainComplex.HomComplex.homologyAddEquiv _ _ (n : ℤ)).symm
          (.mk (CochainComplex.HomComplex.Cocycle.fromSingleMk
            (f ≫ (I.cochainComplexXIso n n rfl).inv) (zero_add _)
            m (by omega)
            (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf])))) := by
  rw [extRightDerivedAddEquiv_apply]
  congr 2
  exact I.extEquivCohomologyClass_extMk f m hm hf

open CochainComplex.HomComplex

omit [EnoughInjectives C] in
private theorem extAddEquivCohomologyClass_naturality
    {X' Y' : C} {J : InjectiveResolution Y'} {g : Y ⟶ Y'}
    (φ : Hom I J g) (f : X' ⟶ X) (x : Abelian.Ext.{w} X Y n) :
    J.extAddEquivCohomologyClass
        (((Abelian.Ext.mk₀ f).comp x (zero_add _)).comp
          (Abelian.Ext.mk₀ g) (add_zero _)) =
      ExtRightDerived.classMap ((CochainComplex.singleFunctor C 0).map f) φ.hom' (n : ℤ)
        (I.extAddEquivCohomologyClass x) := by
  obtain ⟨a, ha, rfl⟩ := I.extMk_surjective x (n + 1) rfl
  change J.extEquivCohomologyClass _ =
    ExtRightDerived.classMap _ _ _ (I.extEquivCohomologyClass _)
  rw [I.mk₀_comp_extMk, extMk_comp_mk₀ _ _ _ _ φ]
  simp only [extEquivCohomologyClass_extMk, ExtRightDerived.classMap_mk]
  rw [← Cocycle.fromSingleMk_precomp, ← Cocycle.fromSingleMk_postcomp]
  congr 2
  simp [φ.hom'_f n n rfl, Category.assoc]

omit [HasExt.{w} C] in
private theorem homComplexHomologyRightDerivedIso_hom_naturality
    {Y' : C} {J : InjectiveResolution Y'} {g : Y ⟶ Y'}
    (φ : Hom I J g) :
    homologyMap (ExtRightDerived.map
        ((CochainComplex.singleFunctor C 0).map (𝟙 X)) φ.hom') (n : ℤ) ≫
        (J.homComplexHomologyRightDerivedIso X n).hom =
      (I.homComplexHomologyRightDerivedIso X n).hom ≫
        ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).map g := by
  let F := preadditiveCoyoneda.obj (Opposite.op X)
  let E₀ := (homologyFunctor _ _ (n : ℤ)).mapIso
    (homComplexSingleIso X I.cochainComplex)
  let E₁ := (homologyFunctor _ _ (n : ℤ)).mapIso
    (homComplexSingleIso X J.cochainComplex)
  let C₀ := I.isoRightDerivedObjCochain F n
  let C₁ := J.isoRightDerivedObjCochain F n
  have hE := congrArg ((homologyFunctor _ _ (n : ℤ)).map)
    (homComplexSingleIso_naturality (𝟙 X) φ.hom')
  simp only [Functor.map_comp, Functor.map_id, CategoryTheory.op_id,
    NatTrans.mapHomologicalComplex_id, NatTrans.id_app, Category.id_comp] at hE
  have hE' : homologyMap (ExtRightDerived.map
      ((CochainComplex.singleFunctor C 0).map (𝟙 X)) φ.hom') (n : ℤ) ≫ E₁.hom =
      E₀.hom ≫ homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') (n : ℤ) := by
    simpa only [E₀, E₁, F, Functor.mapIso_hom, homologyFunctor_map,
      Functor.map_id] using hE
  exact iso_comparison_naturality E₀ E₁ C₀ C₁ _ _ _ hE'
    (isoRightDerivedObjCochain_hom_naturality F φ n)

/-- The comparison intertwines every original coefficient map with the actual
map of the original right-derived additive Hom functor. Any supplied resolution
lift may be used; it does not change the right-hand side. -/
theorem extRightDerivedAddEquiv_naturality_right
    {Y' : C} {J : InjectiveResolution Y'} {g : Y ⟶ Y'}
    (φ : Hom I J g) (x : Abelian.Ext.{w} X Y n) :
    J.extRightDerivedAddEquiv X n (x.comp (Abelian.Ext.mk₀ g) (add_zero _)) =
      ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).map g
        (I.extRightDerivedAddEquiv X n x) := by
  let a := (homologyAddEquiv _ _ (n : ℤ)).symm (I.extAddEquivCohomologyClass x)
  have h := I.extAddEquivCohomologyClass_naturality X n φ (𝟙 X) x
  simp only [Abelian.Ext.mk₀_id_comp] at h
  have hH := ExtRightDerived.homologyAddEquiv_naturality
    ((CochainComplex.singleFunctor C 0).map (𝟙 X)) φ.hom' (n : ℤ) a
  have ha : (homologyAddEquiv _ _ (n : ℤ)).symm
      (J.extAddEquivCohomologyClass (x.comp (Abelian.Ext.mk₀ g) (add_zero _))) =
      homologyMap (ExtRightDerived.map
        ((CochainComplex.singleFunctor C 0).map (𝟙 X)) φ.hom') (n : ℤ) a := by
    apply (homologyAddEquiv _ _ (n : ℤ)).injective
    rw [AddEquiv.apply_symm_apply, hH]
    simpa only [a, AddEquiv.apply_symm_apply] using h
  rw [extRightDerivedAddEquiv_apply, ha, extRightDerivedAddEquiv_apply]
  exact ConcreteCategory.congr_hom
    (I.homComplexHomologyRightDerivedIso_hom_naturality X n φ) a

/-- The original integer-resolution cocycle is sent to its actual homology class
under the native right-derived comparison. -/
theorem extRightDerivedAddEquiv_cocycle
    (f : X ⟶ I.cochainComplex.X (n : ℤ))
    (hf : f ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0) :
    I.extRightDerivedAddEquiv X n
        (I.extEquivCohomologyClass.symm
          (.mk (Cocycle.fromSingleMk f (zero_add (n : ℤ)) ((n : ℤ) + 1) rfl hf))) =
      let H := ((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
        (.up ℤ)).obj I.cochainComplex
      (I.isoRightDerivedObjCochain (preadditiveCoyoneda.obj (Opposite.op X)) n).inv
        (H.homologyπ (n : ℤ) ((H.sc (n : ℤ)).abCyclesIso.inv ⟨f, by
          change f ≫ I.cochainComplex.d (n : ℤ) ((ComplexShape.up ℤ).next (n : ℤ)) = 0
          rw [CochainComplex.next ℤ (n : ℤ)]
          exact hf⟩)) := by
  rw [extRightDerivedAddEquiv_apply]
  change (I.homComplexHomologyRightDerivedIso X n).hom
    ((homologyAddEquiv _ _ (n : ℤ)).symm
      (I.extEquivCohomologyClass (I.extEquivCohomologyClass.symm _))) = _
  rw [Equiv.apply_symm_apply]
  change (I.isoRightDerivedObjCochain (preadditiveCoyoneda.obj (Opposite.op X)) n).inv
    (homologyMap (homComplexSingleIso X I.cochainComplex).hom (n : ℤ)
      ((homologyAddEquiv _ _ (n : ℤ)).symm _)) = _
  rw [homology_homComplexSingleIso_fromSingleMk]

open CategoryTheory.Abelian

omit [EnoughInjectives C] [HasExt.{w} C] in
private theorem zeroCocycle_closed (f : X ⟶ Y) :
    ((f ≫ I.ι.f 0) ≫ (I.cochainComplexXIso 0 0 rfl).inv) ≫
      I.cochainComplex.d 0 1 = 0 := by
  have hf : (f ≫ I.ι.f 0) ≫ I.cocomplex.d 0 1 = 0 := by
    rw [Category.assoc, I.ι.comm 0 1]
    simp
  rw [I.cochainComplex_d 0 1 0 1 rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc, zero_comp] using
    congrArg (fun k => k ≫ (I.cochainComplexXIso 1 1 rfl).inv) hf

omit [EnoughInjectives C] [HasExt.{w} C] in
private def zeroCocycleCycles (f : X ⟶ Y) :
    (((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
      (.up ℤ)).obj I.cochainComplex).cycles 0 :=
  (HomologicalComplex.sc _ 0).abCyclesIso.inv
    ⟨(f ≫ I.ι.f 0) ≫ (I.cochainComplexXIso 0 0 rfl).inv, by
      change ((f ≫ I.ι.f 0) ≫ (I.cochainComplexXIso 0 0 rfl).inv) ≫
        I.cochainComplex.d 0 ((ComplexShape.up ℤ).next 0) = 0
      rw [CochainComplex.next ℤ (0 : ℤ)]
      exact I.zeroCocycle_closed X f⟩

omit [EnoughInjectives C] [HasExt.{w} C] in
private theorem zeroCocycleCycles_eq (f : X ⟶ Y) :
    I.zeroCocycleCycles X f =
      I.toRightDerivedZeroCochainCycles (preadditiveCoyoneda.obj (Opposite.op X)) f := by
  let F := preadditiveCoyoneda.obj (Opposite.op X)
  let H := (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  apply (AddCommGrpCat.mono_iff_injective (H.iCycles 0)).mp inferInstance
  dsimp only [zeroCocycleCycles]
  erw [HomologicalComplex.iCycles, ShortComplex.abCyclesIso_inv_apply_iCycles]
  exact (ConcreteCategory.congr_hom
    (I.toRightDerivedZeroCochainCycles_comp_iCycles F) f).symm

private theorem extRightDerivedAddEquiv_mk₀_aux (f : X ⟶ Y) :
    I.extRightDerivedAddEquiv X 0 (Ext.mk₀ f) =
      let F := preadditiveCoyoneda.obj (Opposite.op X)
      let H := (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
      (I.isoRightDerivedObjCochain F 0).inv (H.homologyπ 0 (I.zeroCocycleCycles X f)) := by
  let F := preadditiveCoyoneda.obj (Opposite.op X)
  let E := I.isoRightDerivedObjCochain F 0
  let a := (f ≫ I.ι.f 0) ≫ (I.cochainComplexXIso 0 0 rfl).inv
  have ha : a ≫ I.cochainComplex.d 0 1 = 0 := I.zeroCocycle_closed X f
  rw [← I.extMk_ι_zero f, extRightDerivedAddEquiv_extMk]
  change E.inv (homologyMap (homComplexSingleIso X I.cochainComplex).hom 0
    ((homologyAddEquiv _ _ (0 : ℤ)).symm
      (.mk (Cocycle.fromSingleMk a (zero_add (0 : ℤ)) 1 rfl ha)))) = _
  exact congrArg (fun z => E.inv z)
    (homology_homComplexSingleIso_fromSingleMk X I.cochainComplex (0 : ℤ) a ha)

/-- In degree zero the comparison is the original transformation to the zeroth
right-derived functor, evaluated at the original morphism. -/
theorem extRightDerivedAddEquiv_mk₀ (f : X ⟶ Y) :
    I.extRightDerivedAddEquiv X 0 (Ext.mk₀ f) =
      (preadditiveCoyoneda.obj (Opposite.op X)).toRightDerivedZero.app Y f := by
  let F := preadditiveCoyoneda.obj (Opposite.op X)
  let H := (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let E := I.isoRightDerivedObjCochain F 0
  rw [I.extRightDerivedAddEquiv_mk₀_aux X f, I.zeroCocycleCycles_eq X f]
  have h₀ : F.toRightDerivedZero.app Y ≫ E.hom =
      I.toRightDerivedZeroCochainCycles F ≫ H.homologyπ 0 :=
    I.toRightDerivedZero_comp_isoRightDerivedObjCochain F
  have h₁ : (I.toRightDerivedZeroCochainCycles F ≫ H.homologyπ 0) ≫ E.inv =
      F.toRightDerivedZero.app Y := by
    rw [← h₀, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h₂ := ConcreteCategory.congr_hom h₁ f
  change E.inv (H.homologyπ 0 (I.toRightDerivedZeroCochainCycles F f)) =
    F.toRightDerivedZero.app Y f at h₂
  change E.inv (H.homologyπ 0 (I.toRightDerivedZeroCochainCycles F f)) =
    F.toRightDerivedZero.app Y f
  exact h₂

end CategoryTheory.InjectiveResolution

/- Naturality in the additive functor uses the shared native extension comparison. -/
universe u' v'

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G)
  {M : C} (I : InjectiveResolution M)

/-- Naturality in the additive functor of the original integer-cochain
resolution comparison. In particular, its left arrow is native
`NatTrans.rightDerived`, not an independently chosen comparison. -/
@[reassoc]
theorem isoRightDerivedObjCochain_hom_natTrans (n : ℕ) :
    (NatTrans.rightDerived α n).app M ≫ (I.isoRightDerivedObjCochain G n).hom =
      (I.isoRightDerivedObjCochain F n).hom ≫
        homologyMap ((NatTrans.mapHomologicalComplex α (.up ℤ)).app I.cochainComplex)
          (n : ℤ) := by
  let E₀ := ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  let E₁ := ((G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  let D₀ := (homologyFunctor D (.up ℤ) (n : ℤ)).mapIso
    (I.cocomplex.mapExtendIso F ComplexShape.embeddingUpNat)
  let D₁ := (homologyFunctor D (.up ℤ) (n : ℤ)).mapIso
    (I.cocomplex.mapExtendIso G ComplexShape.embeddingUpNat)
  have hδ := congrArg ((homologyFunctor D (.up ℤ) (n : ℤ)).map)
    (I.cocomplex.mapExtendIso_hom_natTrans F G α ComplexShape.embeddingUpNat)
  simp only [Functor.map_comp] at hδ
  change homologyMap
      ((NatTrans.mapHomologicalComplex α (.up ℤ)).app I.cochainComplex) (n : ℤ) ≫
        D₁.hom = D₀.hom ≫ homologyMap
      (extendMap ((NatTrans.mapHomologicalComplex α (.up ℕ)).app I.cocomplex)
        ComplexShape.embeddingUpNat) (n : ℤ) at hδ
  have hE := HomologicalComplex.extendHomologyIso_hom_naturality
    ((NatTrans.mapHomologicalComplex α (.up ℕ)).app I.cocomplex)
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  change homologyMap
      (extendMap ((NatTrans.mapHomologicalComplex α (.up ℕ)).app I.cocomplex)
        ComplexShape.embeddingUpNat) (n : ℤ) ≫ E₁.hom =
    E₀.hom ≫ homologyMap
      ((NatTrans.mapHomologicalComplex α (.up ℕ)).app I.cocomplex) n at hE
  apply (cancel_mono D₁.hom).mp
  simp only [isoRightDerivedObjCochain_hom, Category.assoc]
  change (NatTrans.rightDerived α n).app M ≫ (I.isoRightDerivedObj G n).hom ≫
      E₁.inv ≫ D₁.inv ≫ D₁.hom =
    (I.isoRightDerivedObj F n).hom ≫ E₀.inv ≫ D₀.inv ≫
      homologyMap ((NatTrans.mapHomologicalComplex α (.up ℤ)).app I.cochainComplex)
        (n : ℤ) ≫ D₁.hom
  rw [hδ]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_mono E₁.hom).mp
  simp only [Category.assoc]
  rw [hE]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [InjectiveResolution.rightDerived_app_eq α I n]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Native right-derived natural transformation computed on the supplied integer
resolution, with exactly the existing comparison isomorphisms. -/
theorem rightDerived_app_eq_cochain (n : ℕ) :
    (NatTrans.rightDerived α n).app M =
      (I.isoRightDerivedObjCochain F n).hom ≫
        homologyMap ((NatTrans.mapHomologicalComplex α (.up ℤ)).app I.cochainComplex)
          (n : ℤ) ≫
        (I.isoRightDerivedObjCochain G n).inv := by
  apply (cancel_mono (I.isoRightDerivedObjCochain G n).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact isoRightDerivedObjCochain_hom_natTrans α I n

end CategoryTheory.InjectiveResolution

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] (X : C) (n : ℕ) {H : C ⥤ AddCommGrpCat.{v}}
  (e : (preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n ≅ H)

/-- Composing the actual Ext comparison with a specified natural isomorphism
retains coefficient naturality, without unfolding the isomorphism's construction. -/
theorem extRightDerivedAddEquiv_trans_naturality
    {Y Y' : C} {I : InjectiveResolution Y} {J : InjectiveResolution Y'}
    {g : Y ⟶ Y'} (φ : Hom I J g) (x : Abelian.Ext.{w} X Y n) :
    ((J.extRightDerivedAddEquiv X n).trans
      (e.app Y').addCommGroupIsoToAddEquiv) (x.comp (Abelian.Ext.mk₀ g) (add_zero _)) =
    H.map g (((I.extRightDerivedAddEquiv X n).trans
      (e.app Y).addCommGroupIsoToAddEquiv) x) := by
  change e.hom.app Y' (J.extRightDerivedAddEquiv X n
    (x.comp (Abelian.Ext.mk₀ g) (add_zero _))) =
      H.map g (e.hom.app Y (I.extRightDerivedAddEquiv X n x))
  rw [I.extRightDerivedAddEquiv_naturality_right X n φ x]
  exact ConcreteCategory.congr_hom (e.hom.naturality g)
    (I.extRightDerivedAddEquiv X n x)

/-- The composed comparison is independent of the supplied injective resolution. -/
theorem extRightDerivedAddEquiv_trans_eq
    {Y : C} (I J : InjectiveResolution Y) :
    (I.extRightDerivedAddEquiv X n).trans (e.app Y).addCommGroupIsoToAddEquiv =
      (J.extRightDerivedAddEquiv X n).trans (e.app Y).addCommGroupIsoToAddEquiv := by
  let φ : Hom I J (𝟙 Y) :=
    ⟨desc (𝟙 Y) _ _, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        desc_commutes_zero (𝟙 Y) J I⟩
  ext x
  have h := extRightDerivedAddEquiv_trans_naturality X n e φ x
  rw [Abelian.Ext.comp_mk₀_id, Functor.map_id] at h
  exact h.symm

end CategoryTheory.InjectiveResolution
