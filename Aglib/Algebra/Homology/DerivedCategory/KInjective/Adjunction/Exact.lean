/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Adjunction.InjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# The original pointwise derived adjunction for an exact left adjoint

The native localization of the exact left adjoint expresses the installed
pointwise adjunction inverse through the original cochain counit. Its native
shift square identifies every shifted supplied-resolution comparison with one
and the same resolution counit. No global derived adjunction is assumed.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u v w u' v' w' e e'

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

private theorem derived_map_surjective_exact (K L : CochainComplex C ℤ)
    [L.IsKInjective] :
    Function.Surjective (fun p : K ⟶ L => DerivedCategory.Q.map p) := by
  intro f
  obtain ⟨p, rfl⟩ := (CochainComplex.homotopyDerivedHomEquiv K L).surjective f
  obtain ⟨q, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective p
  exact ⟨q, (CochainComplex.homotopyDerivedHomEquiv_map K L q).symm⟩

/-- The same degreewise counit commutes with the original cochain shifts. -/
instance mapHomologicalComplex_counit_commShift :
    (adj.mapHomologicalComplex (.up ℤ)).counit.CommShift ℤ where
  shift_comm k := by
    ext L n
    simp [Functor.commShiftIso_comp_hom_app, mapHomologicalComplex]

/-- The native exact-functor factor followed by the original chain counit. -/
def cochainDerivedCounit :
    G.mapHomologicalComplex (.up ℤ) ⋙ (DerivedCategory.Q ⋙ F.mapDerivedCategory) ⟶
      DerivedCategory.Q :=
  Functor.whiskerLeft (G.mapHomologicalComplex (.up ℤ)) F.mapDerivedCategoryFactors.hom ≫
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (adj.mapHomologicalComplex (.up ℤ)).counit DerivedCategory.Q ≫
        (Functor.leftUnitor _).hom

@[simp]
theorem cochainDerivedCounit_app (L : CochainComplex D ℤ) :
    (cochainDerivedCounit adj).app L =
      F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj L) ≫
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app L) := by
  simp [cochainDerivedCounit]

instance cochainDerivedCounit_commShift : (cochainDerivedCounit adj).CommShift ℤ := by
  dsimp only [cochainDerivedCounit]
  infer_instance

/-- Every derived arrow into the actual right-adjoint model has its original
pointwise adjoint, expressed using the native exact left-adjoint functor. -/
theorem cochainDerivedHomEquivOfKInjective_symm_eq_map_counit
    (K : CochainComplex C ℤ) (L : CochainComplex D ℤ)
    [L.IsKInjective] [CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj L)]
    (g : DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj L)) :
    (adj.cochainDerivedHomEquivOfKInjective K L).symm g =
      F.mapDerivedCategoryFactors.inv.app K ≫ F.mapDerivedCategory.map g ≫
        (cochainDerivedCounit adj).app L := by
  obtain ⟨p, rfl⟩ := derived_map_surjective_exact K _ g
  rw [cochainDerivedHomEquivOfKInjective_symm_map, cochainDerivedCounit_app,
    Adjunction.homEquiv_counit, Functor.map_comp]
  rw [F.mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]

/-- This source square applies to arbitrary derived arrows, not only original
module morphisms or localized source-chain maps. -/
theorem cochainDerivedHomEquivOfKInjective_symm_naturality_derived
    {K K' : CochainComplex C ℤ} (L : CochainComplex D ℤ)
    [L.IsKInjective] [CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj L)]
    (a : DerivedCategory.Q.obj K' ⟶ DerivedCategory.Q.obj K)
    (g : DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj L)) :
    (adj.cochainDerivedHomEquivOfKInjective K' L).symm (a ≫ g) =
      F.mapDerivedCategoryFactors.inv.app K' ≫ F.mapDerivedCategory.map a ≫
        F.mapDerivedCategoryFactors.hom.app K ≫
          (adj.cochainDerivedHomEquivOfKInjective K L).symm g := by
  rw [cochainDerivedHomEquivOfKInjective_symm_eq_map_counit,
    cochainDerivedHomEquivOfKInjective_symm_eq_map_counit, Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

/-- Native shift transport of the same counit. -/
@[reassoc]
theorem cochainDerivedCounit_shift (L : CochainComplex D ℤ) (k : ℤ) :
    F.mapDerivedCategory.map ((DerivedCategory.Q.commShiftIso k).inv.app
        ((G.mapHomologicalComplex (.up ℤ)).obj L)) ≫
      F.mapDerivedCategory.map (DerivedCategory.Q.map
        (((G.mapHomologicalComplex (.up ℤ)).commShiftIso k).inv.app L)) ≫
      (cochainDerivedCounit adj).app (L⟦k⟧) ≫
      (DerivedCategory.Q.commShiftIso k).hom.app L =
    (F.mapDerivedCategory.commShiftIso k).hom.app
        (DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj L)) ≫
      ((cochainDerivedCounit adj).app L)⟦k⟧' := by
  have h := NatTrans.shift_app_comm (cochainDerivedCounit adj) k L
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map,
    Category.assoc] at h
  rw [← h]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

variable [EnoughInjectives D]

/-- One counit on the installed right-derived value, through the original
supplied-resolution comparison and original resolution inclusion. -/
def injectiveResolutionDerivedCounit {N : D} (I : InjectiveResolution N) :
    F.mapDerivedCategory.obj (DerivedCategory.Plus.ι.obj
      (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor D 0).obj N))) ⟶
        (DerivedCategory.singleFunctor D 0).obj N :=
  F.mapDerivedCategory.map (rightDerivedResolutionIso (G := G) I).inv ≫
    (cochainDerivedCounit adj).app I.cochainComplex ≫
      (asIso (DerivedCategory.Q.map I.ι')).inv

/-- Both original supplied-resolution shift comparisons give exactly the
shift of the single unshifted counit. -/
@[reassoc]
theorem injectiveResolutionDerivedCounit_shift {N : D}
    (I : InjectiveResolution N) (k : ℤ) :
    F.mapDerivedCategory.map (rightDerivedResolutionShiftIso (G := G) I k).inv ≫
      (cochainDerivedCounit adj).app (I.cochainComplex⟦k⟧) ≫
        (resolutionShiftIso I k).inv =
      (F.mapDerivedCategory.commShiftIso k).hom.app
          (DerivedCategory.Plus.ι.obj
            (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor D 0).obj N))) ≫
        (injectiveResolutionDerivedCounit adj I)⟦k⟧' := by
  dsimp only [rightDerivedResolutionShiftIso, resolutionShiftIso,
    injectiveResolutionDerivedCounit, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
  simp only [Functor.map_comp, Category.assoc, Iso.app_inv, Iso.symm_inv]
  rw [cochainDerivedCounit_shift_assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc]

omit [EnoughInjectives D] in
private theorem singleImageIso_inv_comp_exactFactor (M : C) :
    (singleImageIso (F := F) M).inv ≫
        F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj M) =
      (F.mapDerivedCategorySingleFunctor 0).inv.app M := by
  change DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app M) ≫ _ = _
  rw [← F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app M]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- The inverse of the original single comparison retains the same native
single, cochain adjunction and two resolution isomorphisms. -/
theorem singleDerivedHomEquivOfInjectiveResolution_symm_apply_model
    (M : C) {N : D} (I : InjectiveResolution N) (k : ℤ)
    (g : (DerivedCategory.singleFunctor C 0).obj M ⟶
      (DerivedCategory.Plus.ι.obj
        (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor D 0).obj N)))⟦k⟧) :
    (adj.singleDerivedHomEquivOfInjectiveResolution M I k).symm g =
      (singleImageIso (F := F) M).inv ≫
        (adj.cochainDerivedHomEquivOfInjectiveResolution I k
          ((CochainComplex.singleFunctor C 0).obj M)).symm
            (g ≫ (rightDerivedResolutionShiftIso (G := G) I k).inv) ≫
          (resolutionShiftIso I k).inv := by
  change (singleImageIso (F := F) M).inv ≫
      (adj.cochainDerivedHomEquivOfInjectiveResolution I k
        ((CochainComplex.singleFunctor C 0).obj M)).symm
          (𝟙 _ ≫ g ≫ (rightDerivedResolutionShiftIso (G := G) I k).inv) ≫
        (resolutionShiftIso I k).inv = _
  rw [Category.id_comp]

omit [EnoughInjectives D] in
/-- The supplied-resolution pointwise inverse uses the original counit after
the native exact-functor localization factor. -/
theorem cochainDerivedHomEquivOfInjectiveResolution_symm_eq_map_counit
    {N : D} (I : InjectiveResolution N) (k : ℤ) (K : CochainComplex C ℤ)
    (g : DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj
        ((G.mapHomologicalComplex (.up ℤ)).obj (I.cochainComplex⟦k⟧))) :
    (adj.cochainDerivedHomEquivOfInjectiveResolution I k K).symm g =
      F.mapDerivedCategoryFactors.inv.app K ≫ F.mapDerivedCategory.map g ≫
        (cochainDerivedCounit adj).app (I.cochainComplex⟦k⟧) := by
  let L := I.cochainComplex⟦k⟧
  let : L.IsStrictlyGE (-k) := I.cochainComplex.isStrictlyGE_shift 0 k (-k) (by omega)
  let : ∀ n : ℤ, Injective (L.X n) := fun n => by
    change Injective (I.cochainComplex.X (n + k))
    infer_instance
  let : L.IsKInjective := CochainComplex.isKInjective_of_injective L (-k)
  let := adj.isKInjective_map_of_injectiveComplex L (-k)
  exact adj.cochainDerivedHomEquivOfKInjective_symm_eq_map_counit K L g

/-- Every degree uses the same original counit, shifted by that degree, after
the native derived image of the supplied arrow. -/
theorem singleDerivedHomEquivOfInjectiveResolution_symm_eq_map_counit
    (M : C) {N : D} (I : InjectiveResolution N) (k : ℤ)
    (g : (DerivedCategory.singleFunctor C 0).obj M ⟶
      (DerivedCategory.Plus.ι.obj
        (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor D 0).obj N)))⟦k⟧) :
    (adj.singleDerivedHomEquivOfInjectiveResolution M I k).symm g =
      (F.mapDerivedCategorySingleFunctor 0).inv.app M ≫
        ShiftedHom.map g F.mapDerivedCategory ≫
          (injectiveResolutionDerivedCounit adj I)⟦k⟧' := by
  rw [singleDerivedHomEquivOfInjectiveResolution_symm_apply_model,
    cochainDerivedHomEquivOfInjectiveResolution_symm_eq_map_counit,
    Functor.map_comp]
  simp only [Category.assoc]
  rw [injectiveResolutionDerivedCounit_shift]
  rw [← Category.assoc (singleImageIso (F := F) M).inv,
    singleImageIso_inv_comp_exactFactor]
  simp only [ShiftedHom.map, Category.assoc]

/-- The original supplied-resolution inverse is natural for every Ext class in its
source. Exactness is required only for the left adjoint; the same original counit
and native shift comparisons occur in every degree. -/
theorem singleDerivedHomEquivOfInjectiveResolution_symm_comp_ext
    [HasExt.{e} C] [HasExt.{e'} D] {M M' : C} {N : D}
    (I : InjectiveResolution N) {r : ℕ} (α : CategoryTheory.Abelian.Ext M M' r)
    (j q : ℤ) (h : j + (r : ℤ) = q)
    (g : ShiftedHom ((DerivedCategory.singleFunctor C 0).obj M')
      (DerivedCategory.Plus.ι.obj
        (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor D 0).obj N))) j) :
    (adj.singleDerivedHomEquivOfInjectiveResolution M I q).symm (α.hom.comp g h) =
      (α.mapExactFunctor F).hom.comp
        ((adj.singleDerivedHomEquivOfInjectiveResolution M' I j).symm g) h := by
  rw [singleDerivedHomEquivOfInjectiveResolution_symm_eq_map_counit,
    singleDerivedHomEquivOfInjectiveResolution_symm_eq_map_counit,
    CategoryTheory.Abelian.Ext.mapExactFunctor_hom, ShiftedHom.map_comp]
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  rw [← (shiftFunctor (DerivedCategory D) (r : ℤ)).map_comp_assoc,
    Iso.hom_inv_id_app]
  erw [Functor.map_id, Category.id_comp]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun z => (F.mapDerivedCategorySingleFunctor 0).inv.app M ≫
      α.hom.map F.mapDerivedCategory ≫ (g.map F.mapDerivedCategory)⟦(r : ℤ)⟧' ≫ z)
      ((shiftFunctorAdd' (DerivedCategory D) j (r : ℤ) q h).inv.naturality
        (injectiveResolutionDerivedCounit adj I)).symm

end CategoryTheory.Adjunction
