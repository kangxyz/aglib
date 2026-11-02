/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The original square of localized exact functors -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃ u₄ v₄ w₄

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  {D : Type u₄} [Category.{v₄} D] [Abelian D] [HasDerivedCategory.{w₄} D]
  (F : A ⥤ B) (H : B ⥤ D) (G : A ⥤ C) (V : C ⥤ D)
  [F.Additive] [H.Additive] [G.Additive] [V.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  (e : G ⋙ V ≅ F ⋙ H)

/-- The original exact square localized with the native composition factors. -/
def mapDerivedCategorySquareIso :
    G.mapDerivedCategory ⋙ V.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ H.mapDerivedCategory :=
  mapDerivedCategoryCompIso G V ≪≫
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) _ _ _ _
      (isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) DerivedCategory.Q) ≪≫
    (mapDerivedCategoryCompIso F H).symm

/-- The localized square retains the original complex square and exact factors. -/
theorem mapDerivedCategorySquareIso_fac (K : CochainComplex A ℤ) :
    V.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
      V.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) =
    (mapDerivedCategorySquareIso F H G V e).hom.app (DerivedCategory.Q.obj K) ≫
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  have hGV := mapDerivedCategoryCompIso_hom_app_Q_obj G V K
  have hFH := mapDerivedCategoryCompIso_hom_app_Q_obj F H K
  simp only [mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    Iso.refl_hom, NatTrans.mapHomologicalComplex_id, NatTrans.id_app] at hGV hFH
  dsimp only [Functor.comp_obj] at hGV hFH
  have hGVid := (DerivedCategory.Q (C := D)).map_id
    (((G ⋙ V).mapHomologicalComplex (.up ℤ)).obj K)
  have hGV := hGV.trans (congrArg
    (fun z => V.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
      V.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫ z)
    ((congrArg (fun z => z ≫ (G ⋙ V).mapDerivedCategoryFactors.inv.app K) hGVid).trans
      (Category.id_comp _)))
  have hFHid := (DerivedCategory.Q (C := D)).map_id
    (((F ⋙ H).mapHomologicalComplex (.up ℤ)).obj K)
  have hFH := hFH.trans (congrArg
    (fun z => H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫ z)
    ((congrArg (fun z => z ≫ (F ⋙ H).mapDerivedCategoryFactors.inv.app K) hFHid).trans
      (Category.id_comp _)))
  have hFHfac : (mapDerivedCategoryCompIso F H).inv.app (DerivedCategory.Q.obj K) ≫
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      (F ⋙ H).mapDerivedCategoryFactors.hom.app K := by
    apply (cancel_epi ((mapDerivedCategoryCompIso F H).hom.app
      (DerivedCategory.Q.obj K))).mp
    rw [Iso.hom_inv_id_app_assoc, hFH]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact (congrArg (fun z => H.mapDerivedCategory.map
      (F.mapDerivedCategoryFactors.hom.app K) ≫ z)
      (Category.comp_id (H.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K)))).symm
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    Localization.Lifting.iso, isoWhiskerRight_hom, whiskerRight_app, Category.assoc]
  rw [hFHfac, Iso.inv_hom_id_app, Category.comp_id, hGV]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

end CategoryTheory.Functor
