/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactTriangleCoherence

/-! # Composition coherence of original exact localized triangles -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
universe uA vA wA uB vB wB uC vC wC uD vD wD

section Composite
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (G : B ⥤ C) (H : C ⥤ D) (N : B ⥤ D)
  [G.Additive] [H.Additive] [N.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits N] [PreservesFiniteColimits N]

/-- The specified exact composite comparison in the inverse-compositor orientation. -/
def mapDerivedCategoryCompositeIso (c : N ≅ G ⋙ H) :
    N.mapDerivedCategory ≅ G.mapDerivedCategory ⋙ H.mapDerivedCategory :=
  mapDerivedCategoryOriginalIso N (G ⋙ H) c ≪≫ (mapDerivedCategoryCompIso G H).symm

/-- The exact composite comparison retains both original localization factors. -/
@[reassoc]
theorem mapDerivedCategoryCompositeIso_fac (c : N ≅ G ⋙ H) (K : CochainComplex B ℤ) :
    (mapDerivedCategoryCompositeIso G H N c).hom.app (DerivedCategory.Q.obj K) ≫
      H.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
      H.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
    N.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app K) := by
  rw [← mapDerivedCategoryCompIso_fac G H K]
  simp only [mapDerivedCategoryCompositeIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  exact mapDerivedCategoryOriginalIso_fac N (G ⋙ H) c K
end Composite

section Triangle
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
  (M : A ⥤ C) (N : B ⥤ D) (P : A ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [M.Additive] [N.Additive] [P.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits M] [PreservesFiniteColimits M]
  [PreservesFiniteLimits N] [PreservesFiniteColimits N]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]

/-- Original coherent exact triangles remain coherent on the native unbounded categories. -/
theorem mapDerivedCategoryTriangleIso_comp
    (σf : F ⋙ G ≅ M) (σk : M ⋙ H ≅ P) (σt : F ⋙ N ≅ P) (c : N ≅ G ⋙ H)
    (hc : σt = isoWhiskerLeft F c ≪≫ (associator F G H).symm ≪≫
      isoWhiskerRight σf H ≪≫ σk) :
    mapDerivedCategoryTriangleIso F N P σt =
      isoWhiskerLeft F.mapDerivedCategory (mapDerivedCategoryCompositeIso G H N c) ≪≫
        (associator F.mapDerivedCategory G.mapDerivedCategory H.mapDerivedCategory).symm ≪≫
        isoWhiskerRight (mapDerivedCategoryTriangleIso F G M σf) H.mapDerivedCategory ≪≫
        mapDerivedCategoryTriangleIso M H P σk := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  apply (cancel_mono (P.mapDerivedCategoryFactors.hom.app K)).mp
  simp only [Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_inv_app,
    Category.id_comp, Category.assoc]
  rw [mapDerivedCategoryTriangleIso_fac, mapDerivedCategoryTriangleIso_fac]
  rw [← H.mapDerivedCategory.map_comp_assoc, mapDerivedCategoryTriangleIso_fac]
  simp only [H.mapDerivedCategory.map_comp, Category.assoc]
  have hn := H.mapDerivedCategoryFactors.hom.naturality
    ((NatIso.mapHomologicalComplex σf (.up ℤ)).hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  have hnC := (mapDerivedCategoryCompositeIso G H N c).hom.naturality
    (F.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnC
  rw [← reassoc_of% hnC]
  have hfac : (mapDerivedCategoryCompositeIso G H N c).hom.app
      (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      H.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      H.mapDerivedCategoryFactors.hom.app (((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj K) =
    N.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K)) :=
    mapDerivedCategoryCompositeIso_fac G H N c ((F.mapHomologicalComplex (.up ℤ)).obj K)
  rw [reassoc_of% hfac]
  have ho : (NatIso.mapHomologicalComplex σt (.up ℤ)).hom.app K =
      (NatIso.mapHomologicalComplex c (.up ℤ)).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (H.mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex σf (.up ℤ)).hom.app K) ≫
        (NatIso.mapHomologicalComplex σk (.up ℤ)).hom.app K := by
    subst σt
    ext n
    simp [NatIso.mapHomologicalComplex]
  rw [ho, Functor.map_comp, Functor.map_comp]
end Triangle
end CategoryTheory.Functor
