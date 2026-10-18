/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Exact functors and the native bounded-below derived single

The native right-derived unit of an exact functor determines the comparison
with its functor on the full derived category. This comparison commutes with
the installed shifts and identifies the native exact-single isomorphism with
the full derived single isomorphism. Consequently, it carries every native
Ext class to its image under the original exact functor.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u v u' v' w w' e e'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasDerivedCategory.{w'} D] (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The original invertible derived unit, followed by the actual plus/full comparisons.
The termwise comparison is retained explicitly. -/
def rightDerivedFunctorPlusCompιFactors :
    DerivedCategory.Plus.Q ⋙ (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) ≅
      CochainComplex.Plus.ι C ⋙
        F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := by
  letI : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  exact (associator _ _ _).symm ≪≫
    isoWhiskerRight (asIso F.rightDerivedFunctorPlusUnit).symm DerivedCategory.Plus.ι ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft F.mapCochainComplexPlus (DerivedCategory.Plus.QCompιIso D) ≪≫
    (associator _ _ _).symm ≪≫
    isoWhiskerRight F.mapCochainComplexPlusCompι DerivedCategory.Q ≪≫
    associator _ _ _

instance : NatTrans.CommShift F.rightDerivedFunctorPlusCompιFactors.hom ℤ := by
  let : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let : NatTrans.CommShift (CategoryTheory.inv F.rightDerivedFunctorPlusUnit) ℤ :=
    NatTrans.CommShift.of_isIso F.rightDerivedFunctorPlusUnit ℤ
  dsimp [rightDerivedFunctorPlusCompιFactors]
  infer_instance

/-- The installed exact derived-category factorization on bounded-below complexes. -/
def mapDerivedCategoryPlusFactors :
    DerivedCategory.Plus.Q ⋙ (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory) ≅
      CochainComplex.Plus.ι C ⋙
        F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (associator _ _ _).symm ≪≫
    isoWhiskerRight (DerivedCategory.Plus.QCompιIso C) F.mapDerivedCategory ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft (CochainComplex.Plus.ι C) F.mapDerivedCategoryFactors

instance : NatTrans.CommShift F.mapDerivedCategoryPlusFactors.hom ℤ := by
  dsimp [mapDerivedCategoryPlusFactors]
  infer_instance

/-- The localization lifting supplied by the original right-derived unit factorization. -/
-- Preserve the existing native lifting instance and its generated data head.
@[nolint defsWithUnderscore]
instance : Localization.Lifting DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C)
    (CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) :=
  ⟨F.rightDerivedFunctorPlusCompιFactors⟩

/-- The localization lifting supplied by the installed full-derived-category factorization. -/
-- Preserve the existing native lifting instance and its generated data head.
@[nolint defsWithUnderscore]
instance : Localization.Lifting DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C)
    (CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory) :=
  ⟨F.mapDerivedCategoryPlusFactors⟩

instance : NatTrans.CommShift
    (Localization.Lifting.iso DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C)
      (CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)).hom ℤ := by
  dsimp [Localization.Lifting.iso]
  infer_instance

instance : NatTrans.CommShift
    (Localization.Lifting.iso DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C)
      (CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory)).hom ℤ := by
  dsimp [Localization.Lifting.iso]
  infer_instance

/-- The unique comparison normalized by the original right-derived unit and the
installed exact derived-category factorization. -/
def rightDerivedFunctorPlusCompιIso :
    F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C)
    _ _ _ _ (Iso.refl
      (CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q))

instance : NatTrans.CommShift F.rightDerivedFunctorPlusCompιIso.hom ℤ := by
  dsimp [rightDerivedFunctorPlusCompιIso]
  infer_instance

/-- Characterization on complexes, retaining the native termwise plus/full comparison. -/
@[reassoc]
theorem rightDerivedFunctorPlusCompιIso_unit (K : CochainComplex.Plus C) :
    (DerivedCategory.Plus.QCompιIso D).inv.app (F.mapCochainComplexPlus.obj K) ≫
        DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
        F.rightDerivedFunctorPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Q.map (F.mapCochainComplexPlusCompι.hom.app K) ≫
        F.mapDerivedCategoryFactors.inv.app K.obj ≫
        F.mapDerivedCategory.map ((DerivedCategory.Plus.QCompιIso C).inv.app K) := by
  let : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  simp only [comp_obj, ObjectProperty.ι_obj, DerivedCategory.Plus.QCompιIso_inv_app,
    ObjectProperty.ι_map, rightDerivedFunctorPlusCompιIso, Localization.liftNatIso_hom,
    Iso.refl_hom, Localization.liftNatTrans_app, Localization.Lifting.iso,
    rightDerivedFunctorPlusCompιFactors, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    asIso_inv, isoWhiskerLeft_hom, NatTrans.comp_app, associator_inv_app, whiskerRight_app,
    NatIso.isIso_inv_app, ObjectProperty.hom_inv, associator_hom_app, whiskerLeft_app,
    DerivedCategory.Plus.QCompιIso_hom_app, mapCochainComplexPlusCompι_hom_app,
    map_id, Category.comp_id, Category.id_comp, NatTrans.id_app, mapDerivedCategoryPlusFactors,
    Iso.trans_inv, isoWhiskerLeft_inv, isoWhiskerRight_inv, Category.assoc, Iso.symm_inv,
    IsIso.hom_inv_id_assoc]
  exact Category.id_comp _

/-- On the original single, the normalized comparison recovers the SAME native
exact-single map; the equality is forced by its installed unit equation. -/
@[reassoc]
theorem rightDerivedFunctorPlusCompιIso_hom_app_singleFunctor_obj (M : C) :
    F.rightDerivedFunctorPlusCompιIso.hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj M) ≫
        (F.mapDerivedCategorySingleFunctor 0).hom.app M =
      DerivedCategory.Plus.ι.map ((F.rightDerivedFunctorPlusSingleIso 0).hom.app M) := by
  let : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let K := (CochainComplex.singleFunctorPlus C 0).obj M
  have hU :
      DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
          F.rightDerivedFunctorPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj K) =
        F.mapDerivedCategoryFactors.inv.app K.obj := by
    simpa using F.rightDerivedFunctorPlusCompιIso_unit K
  change DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
    F.rightDerivedFunctorPlusCompιIso.hom.app
      ((DerivedCategory.Plus.singleFunctor C 0).obj M) = _ at hU
  apply (cancel_epi (DerivedCategory.Plus.ι.map
    (F.rightDerivedFunctorPlusUnit.app K))).mp
  rw [← Category.assoc, hU]
  erw [F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]
  rw [← map_comp, F.rightDerivedFunctorPlusSingleIso_unit]
  rfl

/-- The native exact-single isomorphism intertwines the right-derived action on
every Ext class with the original exact-functor Ext map, including native shifts. -/
theorem rightDerivedFunctorPlusSingleIso_map_homPlus
    [HasExt.{e} C] [HasExt.{e'} D] {M M' : C} {n : ℕ} (α : Ext M M' n) :
    (F.rightDerivedFunctorPlusSingleIso 0).inv.app M ≫
        α.homPlus.map F.rightDerivedFunctorPlus ≫
        ((F.rightDerivedFunctorPlusSingleIso 0).hom.app M')⟦(n : ℤ)⟧' =
      (α.mapExactFunctor F).homPlus := by
  let β := F.rightDerivedFunctorPlusCompιIso
  let s := F.rightDerivedFunctorPlusSingleIso 0
  let μ := F.mapDerivedCategorySingleFunctor 0
  have hS (X : C) :
      β.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≫ μ.hom.app X =
        DerivedCategory.Plus.ι.map (s.hom.app X) :=
    F.rightDerivedFunctorPlusCompιIso_hom_app_singleFunctor_obj X
  have hInv :
      DerivedCategory.Plus.ι.map (s.inv.app M) ≫
          β.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj M) = μ.inv.app M := by
    apply (cancel_mono (μ.hom.app M)).mp
    rw [Category.assoc, hS, ← map_comp]
    simp
    rfl
  have hNat := ShiftedHom.map_naturality α.homPlus β.hom
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp,
    ShiftedHom.comp_map, Ext.homPlus_map] at hNat
  have hTransport :
      ShiftedHom.map (s.inv.app M ≫ α.homPlus.map F.rightDerivedFunctorPlus ≫
          (s.hom.app M')⟦(n : ℤ)⟧') DerivedCategory.Plus.ι =
        DerivedCategory.Plus.ι.map (s.inv.app M) ≫
          (α.homPlus.map F.rightDerivedFunctorPlus).map DerivedCategory.Plus.ι ≫
          (DerivedCategory.Plus.ι.map (s.hom.app M'))⟦(n : ℤ)⟧' := by
    calc
      _ = ((ShiftedHom.mk₀ (0 : ℤ) rfl (s.inv.app M)).comp
          ((α.homPlus.map F.rightDerivedFunctorPlus).comp
            (ShiftedHom.mk₀ (0 : ℤ) rfl (s.hom.app M')) (zero_add _))
          (add_zero _)).map DerivedCategory.Plus.ι := by
        rw [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
      _ = _ := by
        rw [ShiftedHom.map_comp, ShiftedHom.map_comp, ShiftedHom.map_mk₀,
          ShiftedHom.map_mk₀, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp]
  apply DerivedCategory.Plus.ι.map_injective
  apply (cancel_mono ((DerivedCategory.Plus.ι.commShiftIso (n : ℤ)).hom.app
    ((DerivedCategory.Plus.singleFunctor D 0).obj (F.obj M')))).mp
  change ShiftedHom.map (s.inv.app M ≫ α.homPlus.map F.rightDerivedFunctorPlus ≫
    (s.hom.app M')⟦(n : ℤ)⟧') DerivedCategory.Plus.ι =
      (α.mapExactFunctor F).homPlus.map DerivedCategory.Plus.ι
  rw [hTransport, Ext.homPlus_map, Ext.mapExactFunctor_hom, ← hS]
  simp only [map_comp]
  rw [reassoc_of% hNat]
  rw [← Category.assoc, hInv]

end CategoryTheory.Functor
