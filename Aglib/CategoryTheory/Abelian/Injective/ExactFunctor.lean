/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
/-!
# Exact functors and cycles in actual injective resolutions

An exact additive functor sends a resolution to an exact augmented complex.
Lifting from that complex uses injectivity only in the target resolution.
For every compatible lift, `extMk_mapExactFunctor_comp_mk₀` identifies the
original exact-functor Ext map followed by the coefficient map with the actual
mapped resolution cycle. The source-precomposition corollary retains the
normalization used by geometric pullback. Source and target Ext universes
are independent.

Extraction source: `R5Lab.CategoryTheory.Homology.ExtExactFunctorComparison` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex

universe u₁ v₁ u₂ v₂ w₁ w₂

namespace CategoryTheory.InjectiveResolution.ExactFunctor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {A : C} {B : D} (R : InjectiveResolution A) (S : InjectiveResolution B)
  (a : F.obj A ⟶ B)

/-- The exact complex obtained by applying the given functor to the source resolution. -/
abbrev mappedResolution : CochainComplex D ℕ :=
  (F.mapHomologicalComplex (.up ℕ)).obj R.cocomplex

/-- The first lift uses the monic image of the actual source augmentation. -/
def liftZero : F.obj (R.cocomplex.X 0) ⟶ S.cocomplex.X 0 :=
  Injective.factorThru (a ≫ S.ι.f 0) (F.map (R.ι.f 0))

@[reassoc (attr := simp)]
theorem liftZero_commutes : F.map (R.ι.f 0) ≫ liftZero F R S a = a ≫ S.ι.f 0 :=
  Injective.comp_factorThru _ _

/-- Exactness of the mapped augmentation permits the lift in degree one. -/
def liftOne : F.obj (R.cocomplex.X 1) ⟶ S.cocomplex.X 1 :=
  (R.exact₀.map F).descToInjective (liftZero F R S a ≫ S.cocomplex.d 0 1) (by
    change F.map (R.ι.f 0) ≫ liftZero F R S a ≫ S.cocomplex.d 0 1 = 0
    rw [liftZero_commutes_assoc, S.ι_f_zero_comp_complex_d, comp_zero])

@[reassoc]
theorem liftOne_commutes :
    F.map (R.cocomplex.d 0 1) ≫ liftOne F R S a =
      liftZero F R S a ≫ S.cocomplex.d 0 1 :=
  (R.exact₀.map F).comp_descToInjective _ _

/-- Each successor step uses exactness of the mapped source and injectivity of a target term. -/
def liftSucc (n : ℕ)
    (g : F.obj (R.cocomplex.X n) ⟶ S.cocomplex.X n)
    (g' : F.obj (R.cocomplex.X (n + 1)) ⟶ S.cocomplex.X (n + 1))
    (h : F.map (R.cocomplex.d n (n + 1)) ≫ g' = g ≫ S.cocomplex.d n (n + 1)) :
    Σ' g'' : F.obj (R.cocomplex.X (n + 2)) ⟶ S.cocomplex.X (n + 2),
      F.map (R.cocomplex.d (n + 1) (n + 2)) ≫ g'' =
        g' ≫ S.cocomplex.d (n + 1) (n + 2) :=
  ⟨((R.exact_succ n).map F).descToInjective
    (g' ≫ S.cocomplex.d (n + 1) (n + 2)) (by
      change F.map (R.cocomplex.d n (n + 1)) ≫ g' ≫ S.cocomplex.d (n + 1) (n + 2) = 0
      rw [reassoc_of% h, S.cocomplex.d_comp_d, comp_zero]),
    ((R.exact_succ n).map F).comp_descToInjective _ _⟩

/-- An actual lift from the mapped source resolution into the given target resolution. -/
def lift : mappedResolution F R ⟶ S.cocomplex :=
  CochainComplex.mkHom _ _ (liftZero F R S a) (liftOne F R S a)
    (liftOne_commutes F R S a).symm
    (fun n ⟨g, g', h⟩ ↦
      ⟨(liftSucc F R S n g g' h.symm).1, (liftSucc F R S n g g' h.symm).2.symm⟩)

@[reassoc (attr := simp)]
theorem lift_commutes_zero :
    F.map (R.ι.f 0) ≫ (lift F R S a).f 0 = a ≫ S.ι.f 0 := by
  simpa only [lift, CochainComplex.mkHom_f_0] using liftZero_commutes F R S a

variable {F R S}

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The given cycle remains a cycle after applying the functor and any actual cochain lift. -/
theorem mappedCycle_comp_d (φ : mappedResolution F R ⟶ S.cocomplex)
    {T : C} (n : ℕ) (f : T ⟶ R.cocomplex.X n)
    (hf : f ≫ R.cocomplex.d n (n + 1) = 0) :
    (F.map f ≫ φ.f n) ≫ S.cocomplex.d n (n + 1) = 0 := by
  rw [Category.assoc, φ.comm]
  change F.map f ≫ F.map (R.cocomplex.d n (n + 1)) ≫ φ.f (n + 1) = 0
  rw [← Functor.map_comp_assoc, hf, Functor.map_zero, zero_comp]

end CategoryTheory.InjectiveResolution.ExactFunctor

namespace CategoryTheory.InjectiveResolution.ExactFunctor
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {A : C} {B : D} (R : InjectiveResolution A) (S : InjectiveResolution B)
  (a : F.obj A ⟶ B)

/-- Components of the supplied resolution lift after applying the exact functor, extended by
zero in negative degrees. -/
def extendedLiftF (φ : mappedResolution F R ⟶ S.cocomplex) :
    ∀ i : ℤ, F.obj (R.cochainComplex.X i) ⟶ S.cochainComplex.X i
  | Int.ofNat n => F.map (R.cochainComplexXIso n n rfl).hom ≫ φ.f n ≫
      (S.cochainComplexXIso n n rfl).inv
  | Int.negSucc _ => 0

/-- The supplied lift extended by zero, with the exact functor on the source. -/
def extendedLift (φ : mappedResolution F R ⟶ S.cocomplex) :
    (F.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex ⟶ S.cochainComplex where
  f := extendedLiftF F R S φ
  comm' i j hij := by
    change i + 1 = j at hij
    subst j
    cases i with
    | ofNat n =>
      change (F.map (R.cochainComplexXIso n n rfl).hom ≫ φ.f n ≫
        (S.cochainComplexXIso n n rfl).inv) ≫ S.cochainComplex.d n (n + 1) =
        F.map (R.cochainComplex.d n (n + 1)) ≫
        F.map (R.cochainComplexXIso (n + 1) (n + 1) rfl).hom ≫ φ.f (n + 1) ≫
          (S.cochainComplexXIso (n + 1) (n + 1) rfl).inv
      rw [R.cochainComplex_d _ _ n (n + 1) rfl (by simp),
        S.cochainComplex_d _ _ n (n + 1) rfl (by simp)]
      have hcancel : F.map (R.cochainComplexXIso (n + 1) (n + 1) rfl).inv ≫
          F.map (R.cochainComplexXIso (n + 1) (n + 1) rfl).hom = 𝟙 _ := by
        rw [← F.map_comp, Iso.inv_hom_id, F.map_id]
      simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
        reassoc_of% hcancel]
      have hc := φ.comm n (n + 1)
      change φ.f n ≫ S.cocomplex.d n (n + 1) = F.map (R.cocomplex.d n (n + 1)) ≫ φ.f (n + 1) at hc
      rw [reassoc_of% hc]
    | negSucc n =>
      exact (F.map_isZero (R.cochainComplex.isZero_of_isStrictlyGE 0 (Int.negSucc n)
        (by omega))).eq_of_src _ _

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
@[reassoc]
theorem extendedLift_f (φ : mappedResolution F R ⟶ S.cocomplex) (n : ℕ) :
    (extendedLift F R S φ).f n = F.map (R.cochainComplexXIso n n rfl).hom ≫
      φ.f n ≫ (S.cochainComplexXIso n n rfl).inv := rfl

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The augmented triangle for the supplied compatible lift after extension to integer degrees. -/
theorem extendedLift_augmentation (φ : mappedResolution F R ⟶ S.cocomplex)
    (hφ : F.map (R.ι.f 0) ≫ φ.f 0 = a ≫ S.ι.f 0) :
    (F.mapCochainComplexSingleFunctor 0).inv.app A ≫
      (F.mapHomologicalComplex (.up ℤ)).map R.ι' ≫ extendedLift F R S φ =
    (CochainComplex.singleFunctor D 0).map a ≫ S.ι' := by
  have hcancel : F.map (R.cochainComplexXIso 0 0 rfl).inv ≫
      F.map (R.cochainComplexXIso 0 0 rfl).hom = 𝟙 _ := by
    rw [← F.map_comp, Iso.inv_hom_id, F.map_id]
  apply HomologicalComplex.from_single_hom_ext
  simp [HomologicalComplex.comp_f, extendedLift, extendedLiftF,
    InjectiveResolution.ι'_f_zero, CochainComplex.singleFunctor,
    reassoc_of% hcancel,
    Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.map_comp, reassoc_of% hφ, HomologicalComplex.single_map_f_self]

/-- The actual shifted cochain map associated to a resolution cycle. -/
def cycleHom {T : C} {n : ℕ} (f : T ⟶ R.cocomplex.X n)
    (hf : f ≫ R.cocomplex.d n (n + 1) = 0) :
    ShiftedHom ((CochainComplex.singleFunctor C 0).obj T) R.cochainComplex (n : ℤ) :=
  Cocycle.equivHomShift.symm
    (Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso n n rfl).inv) (zero_add _)
      ((n + 1 : ℕ) : ℤ) (by lia)
      (by
        rw [R.cochainComplex_d (n : ℤ) ((n + 1 : ℕ) : ℤ) n (n + 1) rfl rfl]
        simp [reassoc_of% hf]))

theorem extMk_hom_formula [HasExt.{w₁} C] [HasDerivedCategory C] {T : C} {n : ℕ}
    (f : T ⟶ R.cocomplex.X n) (hf : f ≫ R.cocomplex.d n (n + 1) = 0) :
    (R.extMk f (n + 1) rfl hf).hom =
      (cycleHom R f hf).map DerivedCategory.Q ≫ (inv (DerivedCategory.Q.map R.ι'))⟦(n : ℤ)⟧' := by
  rw [R.extMk_hom]
  change (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 _)).comp
    (((cycleHom R f hf).map DerivedCategory.Q).comp
      (ShiftedHom.mk₀ 0 rfl (inv (DerivedCategory.Q.map R.ι') ≫ 𝟙 _)) (zero_add _))
        (add_zero _) = _
  simp only [Category.comp_id, ShiftedHom.mk₀_id_comp, ShiftedHom.comp_mk₀]

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- Applying the functor and the supplied lift preserves the original cycle map. -/
theorem cycleHom_map_lift (φ : mappedResolution F R ⟶ S.cocomplex)
    {T : C} (n : ℕ) (f : T ⟶ R.cocomplex.X n)
    (hf : f ≫ R.cocomplex.d n (n + 1) = 0) :
    cycleHom S (F.map f ≫ φ.f n) (mappedCycle_comp_d φ n f hf) =
      (F.mapCochainComplexSingleFunctor 0).inv.app T ≫
        (cycleHom R f hf).map (F.mapHomologicalComplex (.up ℤ)) ≫
          (extendedLift F R S φ)⟦(n : ℤ)⟧' := by
  have hcancel : F.map (R.cochainComplexXIso n n rfl).inv ≫
      F.map (R.cochainComplexXIso n n rfl).hom = 𝟙 _ := by
    rw [← F.map_comp, Iso.inv_hom_id, F.map_id]
  have hsingle : F.map (singleObjXSelf (.up ℤ) 0 T).inv ≫
      F.map (singleObjXSelf (.up ℤ) 0 T).hom = 𝟙 _ := by
    rw [← F.map_comp, Iso.inv_hom_id, F.map_id]
  have htransport (i j : ℤ) (h : i = j) :
      F.map (eqToHom (congrArg R.cochainComplex.X h)) ≫ extendedLiftF F R S φ j ≫
        eqToHom (congrArg S.cochainComplex.X h.symm) = extendedLiftF F R S φ i := by
    subst j
    simp
  apply Cocycle.equivHomShift.injective
  apply Subtype.ext
  apply (Cochain.fromSingleEquiv (zero_add (n : ℤ))).injective
  simp only [Cochain.fromSingleEquiv, Cochain.fromSingleMk, Cochain.single, XIsoOfEq,
    eqToIso.inv, eqToIso.hom,
    Category.assoc, cycleHom, Nat.cast_add, Nat.cast_one, Cocycle.equivHomShift_symm_apply,
      Cocycle.equivHomShift_apply,
    Cocycle.ofHom_homOf_eq_self, Cocycle.rightUnshift_coe, Cochain.rightUnshift,
      shiftFunctor_obj_X',
    Cocycle.rightShift_coe, Cochain.rightShift, Cocycle.fromSingleMk_coe, Cochain.mk_v,
      right_eq_add,
    shiftFunctor_obj_X, shiftFunctorObjXIso, eqToHom_trans, AddEquiv.coe_mk, Equiv.coe_fn_mk,
      and_self, ↓reduceDIte,
    eqToHom_refl, Category.id_comp, Category.comp_id, Iso.inv_hom_id_assoc, Functor.comp_obj,
    Functor.mapCochainComplexSingleFunctor, ShiftedHom.map, extendedLift, Cocycle.ofHom_coe,
      Cochain.ofHom_comp,
    Cochain.comp_zero_cochain_v, Functor.mapHomologicalComplex_obj_X, Cochain.ofHom_v,
    Functor.mapHomologicalComplex_map_f, Cocycle.homOf_f, add_zero, Functor.map_dite,
      Functor.map_comp,
    Functor.map_zero, Functor.mapHomologicalComplex_commShiftIso_hom_app_f, shiftFunctor_map_f',
      extendedLiftF,
    Int.ofNat_eq_natCast, Int.reduceAdd, singleMapHomologicalComplex_inv_app_self,
      CategoryTheory.Functor.map_id,
    reassoc_of% hsingle]
  change F.map f ≫ φ.f n ≫ (S.cochainComplexXIso n n rfl).inv =
    F.map f ≫ F.map (R.cochainComplexXIso n n rfl).inv ≫
      F.map (eqToHom (congrArg R.cochainComplex.X (zero_add (n : ℤ)).symm)) ≫
        extendedLiftF F R S φ (0 + (n : ℤ)) ≫
          eqToHom (congrArg S.cochainComplex.X (zero_add (n : ℤ)))
  rw [htransport (n : ℤ) (0 + (n : ℤ)) (zero_add _).symm]
  simp only [extendedLiftF, reassoc_of% hcancel]

/-- The actual augmented triangle after localization, with the prescribed source normalization. -/
theorem derived_augmentation [HasDerivedCategory C] [HasDerivedCategory D]
    (φ : mappedResolution F R ⟶ S.cocomplex)
    (hφ : F.map (R.ι.f 0) ≫ φ.f 0 = a ≫ S.ι.f 0) :
    F.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.ι')) ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app A ≫
        (DerivedCategory.singleFunctor D 0).map a ≫ DerivedCategory.Q.map S.ι' =
    F.mapDerivedCategoryFactors.hom.app R.cochainComplex ≫
      DerivedCategory.Q.map (extendedLift F R S φ) := by
  have haug : (F.mapHomologicalComplex (.up ℤ)).map R.ι' ≫ extendedLift F R S φ =
      (F.mapCochainComplexSingleFunctor 0).hom.app A ≫
        (CochainComplex.singleFunctor D 0).map a ≫ S.ι' := by
    apply (cancel_epi ((F.mapCochainComplexSingleFunctor 0).inv.app A)).mp
    rw [Iso.inv_hom_id_app_assoc]
    exact extendedLift_augmentation F R S a φ hφ
  apply (cancel_epi (F.mapDerivedCategory.map (DerivedCategory.Q.map R.ι'))).mp
  rw [← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    F.mapDerivedCategoryFactors_hom_naturality_assoc, ← Functor.map_comp, haug]
  simp only [Functor.map_comp]
  rw [← F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rfl

/-- Naturality of the derived functor comparison on the original shifted cycle map. -/
theorem derived_cycle_map [HasDerivedCategory C] [HasDerivedCategory D]
    {T : C} (n : ℕ) (f : T ⟶ R.cocomplex.X n)
    (hf : f ≫ R.cocomplex.d n (n + 1) = 0) :
    (F.mapDerivedCategorySingleFunctor 0).inv.app T ≫
      ((cycleHom R f hf).map DerivedCategory.Q).map F.mapDerivedCategory ≫
        (F.mapDerivedCategoryFactors.hom.app R.cochainComplex)⟦(n : ℤ)⟧' =
    DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app T) ≫
      ((cycleHom R f hf).map (F.mapHomologicalComplex (.up ℤ))).map DerivedCategory.Q := by
  have hh := ShiftedHom.map_naturality (cycleHom R f hf) F.mapDerivedCategoryFactors.hom
  simp only [ShiftedHom.comp_map, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at hh
  rw [hh, ← Category.assoc,
    F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The localized cycle after the actual lift, retaining its source normalization. -/
theorem derived_cycle_lift [HasDerivedCategory D]
    (φ : mappedResolution F R ⟶ S.cocomplex)
    {T : C} (n : ℕ) (f : T ⟶ R.cocomplex.X n)
    (hf : f ≫ R.cocomplex.d n (n + 1) = 0) :
    (cycleHom S (F.map f ≫ φ.f n) (mappedCycle_comp_d φ n f hf)).map DerivedCategory.Q =
      DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app T) ≫
        ((cycleHom R f hf).map (F.mapHomologicalComplex (.up ℤ))).map DerivedCategory.Q ≫
          (DerivedCategory.Q.map (extendedLift F R S φ))⟦(n : ℤ)⟧' := by
  rw [cycleHom_map_lift F R S φ n f hf]
  rw [← ShiftedHom.comp_mk₀ ((cycleHom R f hf).map (F.mapHomologicalComplex (.up ℤ)))
    0 rfl (extendedLift F R S φ),
    ← ShiftedHom.mk₀_comp 0 rfl ((F.mapCochainComplexSingleFunctor 0).inv.app T),
    ShiftedHom.map_comp, ShiftedHom.map_comp, ShiftedHom.map_mk₀, ShiftedHom.map_mk₀,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]

/-- The original exact-functor Ext map followed by the actual coefficient map is
represented by the mapped cycle for every compatible lift. -/
theorem extMk_mapExactFunctor_comp_mk₀ [HasExt.{w₁} C] [HasExt.{w₂} D]
    (φ : mappedResolution F R ⟶ S.cocomplex)
    (hφ : F.map (R.ι.f 0) ≫ φ.f 0 = a ≫ S.ι.f 0)
    {T : C} {n : ℕ} (f : T ⟶ R.cocomplex.X n)
    (hf : f ≫ R.cocomplex.d n (n + 1) = 0) :
    ((R.extMk f (n + 1) rfl hf : Abelian.Ext.{w₁} T A n).mapExactFunctor F).comp
      (Abelian.Ext.mk₀ a) (Nat.add_zero n) =
    (S.extMk (F.map f ≫ φ.f n) (n + 1) rfl (mappedCycle_comp_d φ n f hf) :
      Abelian.Ext.{w₂} (F.obj T) B n) := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  have hR : (R.extMk f (n + 1) rfl hf : Abelian.Ext.{w₁} T A n).hom =
      ((cycleHom R f hf).map DerivedCategory.Q).comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl (inv (DerivedCategory.Q.map R.ι'))) (zero_add _) := by
    rw [ShiftedHom.comp_mk₀]
    exact extMk_hom_formula R f hf
  have hRmap : (R.extMk f (n + 1) rfl hf : Abelian.Ext.{w₁} T A n).hom.map F.mapDerivedCategory =
      ((cycleHom R f hf).map DerivedCategory.Q).map F.mapDerivedCategory ≫
        (F.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.ι')))⟦(n : ℤ)⟧' := by
    rw [hR, ShiftedHom.map_comp, ShiftedHom.map_mk₀, ShiftedHom.comp_mk₀]
  apply Abelian.Ext.ext
  rw [Abelian.Ext.comp_hom, Abelian.Ext.mapExactFunctor_hom, Abelian.Ext.mk₀_hom, hRmap,
    ShiftedHom.comp_mk₀]
  rw [extMk_hom_formula S]
  apply (cancel_mono ((DerivedCategory.Q.map S.ι')⟦(n : ℤ)⟧')).mp
  simp only [Category.assoc]
  calc
    _ = (F.mapDerivedCategorySingleFunctor 0).inv.app T ≫
        ((cycleHom R f hf).map DerivedCategory.Q).map F.mapDerivedCategory ≫
          (F.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.ι')) ≫
            (F.mapDerivedCategorySingleFunctor 0).hom.app A ≫
              (DerivedCategory.singleFunctor D 0).map a ≫
                DerivedCategory.Q.map S.ι')⟦(n : ℤ)⟧' := by
      simp only [CategoryTheory.Functor.map_comp]
    _ = (F.mapDerivedCategorySingleFunctor 0).inv.app T ≫
        ((cycleHom R f hf).map DerivedCategory.Q).map F.mapDerivedCategory ≫
          (F.mapDerivedCategoryFactors.hom.app R.cochainComplex ≫
            DerivedCategory.Q.map (extendedLift F R S φ))⟦(n : ℤ)⟧' := by
      rw [derived_augmentation F R S a φ hφ]
    _ = ((F.mapDerivedCategorySingleFunctor 0).inv.app T ≫
        ((cycleHom R f hf).map DerivedCategory.Q).map F.mapDerivedCategory ≫
          (F.mapDerivedCategoryFactors.hom.app R.cochainComplex)⟦(n : ℤ)⟧') ≫
            (DerivedCategory.Q.map (extendedLift F R S φ))⟦(n : ℤ)⟧' := by
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = (DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app T) ≫
        ((cycleHom R f hf).map (F.mapHomologicalComplex (.up ℤ))).map DerivedCategory.Q) ≫
          (DerivedCategory.Q.map (extendedLift F R S φ))⟦(n : ℤ)⟧' := by
      rw [derived_cycle_map F R n f hf]
    _ = (cycleHom S (F.map f ≫ φ.f n) (mappedCycle_comp_d φ n f hf)).map DerivedCategory.Q := by
      rw [Category.assoc]
      exact (derived_cycle_lift F R S φ n f hf).symm
    _ = _ := by
      simp only [← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.comp_id]

/-- The same original Ext-map formula with an arbitrary degree-zero source precomposition. -/
theorem mk₀_comp_extMk_mapExactFunctor_comp_mk₀ [HasExt.{w₁} C] [HasExt.{w₂} D]
    (φ : mappedResolution F R ⟶ S.cocomplex)
    (hφ : F.map (R.ι.f 0) ≫ φ.f 0 = a ≫ S.ι.f 0)
    {T : C} {U : D} {n : ℕ} (f : T ⟶ R.cocomplex.X n)
    (hf : f ≫ R.cocomplex.d n (n + 1) = 0) (b : U ⟶ F.obj T) :
    ((Abelian.Ext.mk₀ b).comp
      ((R.extMk f (n + 1) rfl hf : Abelian.Ext.{w₁} T A n).mapExactFunctor F)
        (Nat.zero_add n)).comp (Abelian.Ext.mk₀ a) (Nat.add_zero n) =
    (S.extMk (b ≫ F.map f ≫ φ.f n) (n + 1) rfl
      (by simpa only [Category.assoc, comp_zero] using
        congrArg (fun z ↦ b ≫ z) (mappedCycle_comp_d φ n f hf)) : Abelian.Ext.{w₂} U B n) := by
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero,
    extMk_mapExactFunctor_comp_mk₀ F R S a φ hφ f hf]
  exact S.mk₀_comp_extMk (F.map f ≫ φ.f n) (n + 1) rfl (mappedCycle_comp_d φ n f hf) b

end CategoryTheory.InjectiveResolution.ExactFunctor
