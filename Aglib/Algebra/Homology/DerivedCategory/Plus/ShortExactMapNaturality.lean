/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.ShortExactMap

/-! # Original component formulas for the exact SES triangle comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u' v' w w'

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {S : ShortComplex (CochainComplex.Plus C)}
  (hS : (S.map (CochainComplex.Plus.ι C)).ShortExact)

/-- The ₁ component is retained by the actual fully faithful bounded-below inclusion. -/
theorem mapTriangleOfSESPlusIso_hom₁_ι :
    DerivedCategory.Plus.ι.map (mapTriangleOfSESPlusIso F hS).hom.hom₁ =
      F.rightDerivedFunctorPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj S.X₁) ≫
        F.mapDerivedCategoryFactors.hom.app S.X₁.obj := by
  unfold mapTriangleOfSESPlusIso
  change ((DerivedCategory.Plus.ι (C := D)).mapTriangle.map
    ((DerivedCategory.Plus.ι (C := D)).mapTriangle.preimage _)).hom₁ = _
  rw [Functor.map_preimage]
  simp only [Functor.mapTriangle_obj, Triangle.mk_obj₁, ObjectProperty.ι_obj, Triangle.mk_obj₂,
    Triangle.mk_obj₃, Triangle.mk_mor₁, ObjectProperty.ι_map, Triangle.mk_mor₂, Triangle.mk_mor₃,
    ObjectProperty.FullSubcategory.comp_hom, Functor.comp_obj, Functor.comp_map,
    Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Functor.mapIso_hom, triangleCategory_comp, TriangleMorphism.comp_hom₁,
    Functor.mapTriangleCompIso_inv_app_hom₁, Functor.mapTriangleIso_hom_app_hom₁,
    Functor.mapTriangleCompIso_hom_app_hom₁, Functor.mapTriangle_map_hom₁, Category.id_comp]
  change F.rightDerivedFunctorPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj S.X₁) ≫
    F.mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj S.X₁.obj)) ≫
      F.mapDerivedCategoryFactors.hom.app S.X₁.obj ≫ 𝟙 _ = _
  exact (congrArg (fun k => F.rightDerivedFunctorPlusCompιIso.hom.app
    (DerivedCategory.Plus.Q.obj S.X₁) ≫ k ≫
      F.mapDerivedCategoryFactors.hom.app S.X₁.obj ≫ 𝟙 _)
        (F.mapDerivedCategory.map_id (DerivedCategory.Q.obj S.X₁.obj))).trans
    (congrArg (fun k => F.rightDerivedFunctorPlusCompιIso.hom.app
      (DerivedCategory.Plus.Q.obj S.X₁) ≫ k)
        ((Category.id_comp (F.mapDerivedCategoryFactors.hom.app S.X₁.obj ≫ 𝟙 _)).trans
          (Category.comp_id (F.mapDerivedCategoryFactors.hom.app S.X₁.obj))))

/-- The ₂ component is retained by the actual fully faithful bounded-below inclusion. -/
theorem mapTriangleOfSESPlusIso_hom₂_ι :
    DerivedCategory.Plus.ι.map (mapTriangleOfSESPlusIso F hS).hom.hom₂ =
      F.rightDerivedFunctorPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj S.X₂) ≫
        F.mapDerivedCategoryFactors.hom.app S.X₂.obj := by
  unfold mapTriangleOfSESPlusIso
  change ((DerivedCategory.Plus.ι (C := D)).mapTriangle.map
    ((DerivedCategory.Plus.ι (C := D)).mapTriangle.preimage _)).hom₂ = _
  rw [Functor.map_preimage]
  simp only [Functor.mapTriangle_obj, Triangle.mk_obj₁, ObjectProperty.ι_obj, Triangle.mk_obj₂,
    Triangle.mk_obj₃, Triangle.mk_mor₁, ObjectProperty.ι_map, Triangle.mk_mor₂, Triangle.mk_mor₃,
    ObjectProperty.FullSubcategory.comp_hom, Functor.comp_obj, Functor.comp_map,
    Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Functor.mapIso_hom, triangleCategory_comp, TriangleMorphism.comp_hom₂,
    Functor.mapTriangleCompIso_inv_app_hom₂, Functor.mapTriangleIso_hom_app_hom₂,
    Functor.mapTriangleCompIso_hom_app_hom₂, Functor.mapTriangle_map_hom₂, Category.id_comp]
  change F.rightDerivedFunctorPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj S.X₂) ≫
    F.mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj S.X₂.obj)) ≫
      F.mapDerivedCategoryFactors.hom.app S.X₂.obj ≫ 𝟙 _ = _
  exact (congrArg (fun k => F.rightDerivedFunctorPlusCompιIso.hom.app
    (DerivedCategory.Plus.Q.obj S.X₂) ≫ k ≫
      F.mapDerivedCategoryFactors.hom.app S.X₂.obj ≫ 𝟙 _)
        (F.mapDerivedCategory.map_id (DerivedCategory.Q.obj S.X₂.obj))).trans
    (congrArg (fun k => F.rightDerivedFunctorPlusCompιIso.hom.app
      (DerivedCategory.Plus.Q.obj S.X₂) ≫ k)
        ((Category.id_comp (F.mapDerivedCategoryFactors.hom.app S.X₂.obj ≫ 𝟙 _)).trans
          (Category.comp_id (F.mapDerivedCategoryFactors.hom.app S.X₂.obj))))

/-- The ₃ component is retained by the actual fully faithful bounded-below inclusion. -/
theorem mapTriangleOfSESPlusIso_hom₃_ι :
    DerivedCategory.Plus.ι.map (mapTriangleOfSESPlusIso F hS).hom.hom₃ =
      F.rightDerivedFunctorPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj S.X₃) ≫
        F.mapDerivedCategoryFactors.hom.app S.X₃.obj := by
  unfold mapTriangleOfSESPlusIso
  change ((DerivedCategory.Plus.ι (C := D)).mapTriangle.map
    ((DerivedCategory.Plus.ι (C := D)).mapTriangle.preimage _)).hom₃ = _
  rw [Functor.map_preimage]
  simp only [Functor.mapTriangle_obj, Triangle.mk_obj₁, ObjectProperty.ι_obj, Triangle.mk_obj₂,
    Triangle.mk_obj₃, Triangle.mk_mor₁, ObjectProperty.ι_map, Triangle.mk_mor₂, Triangle.mk_mor₃,
    ObjectProperty.FullSubcategory.comp_hom, Functor.comp_obj, Functor.comp_map,
    Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Functor.mapIso_hom, triangleCategory_comp, TriangleMorphism.comp_hom₃,
    Functor.mapTriangleCompIso_inv_app_hom₃, Functor.mapTriangleIso_hom_app_hom₃,
    Functor.mapTriangleCompIso_hom_app_hom₃, Functor.mapTriangle_map_hom₃, Category.id_comp]
  change F.rightDerivedFunctorPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj S.X₃) ≫
    F.mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj S.X₃.obj)) ≫
      F.mapDerivedCategoryFactors.hom.app S.X₃.obj ≫ 𝟙 _ = _
  exact (congrArg (fun k => F.rightDerivedFunctorPlusCompιIso.hom.app
    (DerivedCategory.Plus.Q.obj S.X₃) ≫ k ≫
      F.mapDerivedCategoryFactors.hom.app S.X₃.obj ≫ 𝟙 _)
        (F.mapDerivedCategory.map_id (DerivedCategory.Q.obj S.X₃.obj))).trans
    (congrArg (fun k => F.rightDerivedFunctorPlusCompιIso.hom.app
      (DerivedCategory.Plus.Q.obj S.X₃) ≫ k)
        ((Category.id_comp (F.mapDerivedCategoryFactors.hom.app S.X₃.obj ≫ 𝟙 _)).trans
          (Category.comp_id (F.mapDerivedCategoryFactors.hom.app S.X₃.obj))))

end DerivedCategory.Plus
