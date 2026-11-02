/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.PlusExactComparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HorizontalCube

/-! # The original exact square across bounded-below inclusion -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.TwoSquare

universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃ u₄ v₄ w₄

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  [EnoughInjectives B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  [EnoughInjectives C]
  {D : Type u₄} [Category.{v₄} D] [Abelian D] [HasDerivedCategory.{w₄} D]
  (F : A ⥤ B) (H : B ⥤ D) (G : A ⥤ C) (V : C ⥤ D)
  [F.Additive] [H.Additive] [G.Additive] [V.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  (e : G ⋙ V ≅ F ⋙ H)
  (α : TwoSquare G.rightDerivedFunctorPlus F.rightDerivedFunctorPlus
    V.rightDerivedFunctorPlus H.rightDerivedFunctorPlus)
  (hα : ∀ K : CochainComplex.Plus A,
    ExactComparisonSquareEquation F H G V (TwoSquare.mk _ _ _ _ e.hom) α K)

include hα

/-- The actual exact square comparison on each original bounded-below complex. -/
theorem mapDerivedCategorySquareIso_plus_Q (K : CochainComplex.Plus A) :
    V.mapDerivedCategory.map (G.rightDerivedFunctorPlusCompιIso.inv.app
        (DerivedCategory.Plus.Q.obj K)) ≫
      V.rightDerivedFunctorPlusCompιIso.inv.app
        (G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≫
      DerivedCategory.Plus.ι.map (α.app (DerivedCategory.Plus.Q.obj K)) =
    (mapDerivedCategorySquareIso F H G V e).hom.app (DerivedCategory.Q.obj K.obj) ≫
      H.mapDerivedCategory.map (F.rightDerivedFunctorPlusCompιIso.inv.app
        (DerivedCategory.Plus.Q.obj K)) ≫
      H.rightDerivedFunctorPlusCompιIso.inv.app
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) := by
  apply (cancel_mono (DerivedCategory.Plus.ι.map
    (H.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusExactComparison.hom.app K) ≫
      H.rightDerivedFunctorPlusExactComparison.hom.app (F.mapCochainComplexPlus.obj K)))).mp
  simp only [Functor.map_comp, Category.assoc]
  have hb := congrArg (DerivedCategory.Plus.ι.map) (hα K)
  simp only [Functor.map_comp] at hb
  rw [← hb]
  have hV := V.rightDerivedFunctorPlusCompιIso.inv.naturality
    (G.rightDerivedFunctorPlusExactComparison.hom.app K)
  have hH := H.rightDerivedFunctorPlusCompιIso.inv.naturality
    (F.rightDerivedFunctorPlusExactComparison.hom.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hV hH
  rw [← reassoc_of% hV, ← reassoc_of% hH]
  rw [← V.mapDerivedCategory.map_comp_assoc, ← H.mapDerivedCategory.map_comp_assoc]
  rw [G.rightDerivedFunctorPlusCompιIso_inv_exactComparison,
    F.rightDerivedFunctorPlusCompιIso_inv_exactComparison,
    reassoc_of% (V.rightDerivedFunctorPlusCompιIso_inv_exactComparison
      (G.mapCochainComplexPlus.obj K)),
    H.rightDerivedFunctorPlusCompιIso_inv_exactComparison]
  have he : (((TwoSquare.mk G F V H e.hom).mapCochainComplexPlus).app K).hom =
      (NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K.obj := by
    ext n
    change (𝟙 _ ≫ e.hom.app (K.obj.X n) ≫ 𝟙 _) = e.hom.app (K.obj.X n)
    simp only [Category.id_comp, Category.comp_id]
  have hq : DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Q.map ((TwoSquare.mk G F V H e.hom).mapCochainComplexPlus.app K)) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K.obj) := by
    change DerivedCategory.Q.map
      (((TwoSquare.mk G F V H e.hom).mapCochainComplexPlus.app K).hom) = _
    exact congrArg DerivedCategory.Q.map he
  rw [hq]
  exact mapDerivedCategorySquareIso_fac F H G V e K.obj

/-- The fixed exact comparisons identify the original square on all native
bounded-below objects, as an equality of the specified arrows. -/
theorem mapDerivedCategorySquareIso_plus (X : DerivedCategory.Plus A) :
    V.mapDerivedCategory.map (G.rightDerivedFunctorPlusCompιIso.inv.app X) ≫
      V.rightDerivedFunctorPlusCompιIso.inv.app (G.rightDerivedFunctorPlus.obj X) ≫
      DerivedCategory.Plus.ι.map (α.app X) =
    (mapDerivedCategorySquareIso F H G V e).hom.app X.obj ≫
      H.mapDerivedCategory.map (F.rightDerivedFunctorPlusCompιIso.inv.app X) ≫
      H.rightDerivedFunctorPlusCompιIso.inv.app (F.rightDerivedFunctorPlus.obj X) := by
  let sF := TwoSquare.mk _ _ _ _ F.rightDerivedFunctorPlusCompιIso.inv
  let sV := TwoSquare.mk _ _ _ _ V.rightDerivedFunctorPlusCompιIso.inv
  let αU := TwoSquare.mk _ _ _ _ (mapDerivedCategorySquareIso F H G V e).hom
  have hh : whiskerRight G.rightDerivedFunctorPlusCompιIso.inv V.mapDerivedCategory ≫
      (α ≫ₕ sV).natTrans =
      (sF ≫ₕ αU).natTrans ≫
        whiskerLeft F.rightDerivedFunctorPlus H.rightDerivedFunctorPlusCompιIso.inv := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso A)
    intro K
    simpa only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      TwoSquare.hComp_app, sF, sV, αU, Category.assoc,
      DerivedCategory.Plus.Q, ObjectProperty.lift, Functor.comp_obj,
      ObjectProperty.ι_obj] using mapDerivedCategorySquareIso_plus_Q F H G V e α hα K
  simpa only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    TwoSquare.hComp_app, sF, sV, αU, Category.assoc, Functor.comp_obj,
    ObjectProperty.ι_obj] using NatTrans.congr_app hh X

end CategoryTheory.Functor
