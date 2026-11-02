/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactSquare

/-! # Original triangles of exact localized functors

The comparisons use the native exact compositor and the localization of the
specified ordinary isomorphism. Their equations retain all-complex factors.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
universe uA vA wA uB vB wB uC vC wC uD vD wD

section Iso
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  (F G : A ⥤ B) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- Localization of a specified original exact isomorphism. -/
def mapDerivedCategoryOriginalIso (e : F ≅ G) : F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) _ _ _ _
    (isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) DerivedCategory.Q)

/-- The original exact factor equation for the specified isomorphism. -/
@[reassoc]
theorem mapDerivedCategoryOriginalIso_fac (e : F ≅ G) (K : CochainComplex A ℤ) :
    (mapDerivedCategoryOriginalIso F G e).hom.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategoryFactors.hom.app K =
    F.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) := by
  simp only [mapDerivedCategoryOriginalIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, Localization.Lifting.iso,
    isoWhiskerRight_hom, whiskerRight_app, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]
end Iso

section Triangle
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  (F : A ⥤ B) (G : B ⥤ C) (M : A ⥤ C)
  [F.Additive] [G.Additive] [M.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits M] [PreservesFiniteColimits M]

/-- The original exact triangle, with the native compositor. -/
def mapDerivedCategoryTriangleIso (e : F ⋙ G ≅ M) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ M.mapDerivedCategory :=
  mapDerivedCategoryCompIso F G ≪≫ mapDerivedCategoryOriginalIso (F ⋙ G) M e

/-- The native compositor retains the original two exact factors. -/
@[reassoc]
theorem mapDerivedCategoryCompIso_fac (K : CochainComplex A ℤ) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) ≫
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  rw [mapDerivedCategoryCompIso_hom_app_Q_obj]
  simp only [mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    Iso.refl_hom, NatTrans.mapHomologicalComplex_id, NatTrans.id_app,
    Category.assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  have hi := (DerivedCategory.Q (C := C)).map_id
    (((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj K)
  have ht := (congrArg (fun z => z ≫ 𝟙 _) hi).trans (Category.id_comp _)
  exact (congrArg (fun z => G.mapDerivedCategory.map
    (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫ z) ht).trans
    (congrArg (fun z => G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫ z)
      (Category.comp_id (G.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K))))

/-- The triangle comparison retains the specified original complex map. -/
@[reassoc]
theorem mapDerivedCategoryTriangleIso_fac (e : F ⋙ G ≅ M) (K : CochainComplex A ℤ) :
    (mapDerivedCategoryTriangleIso F G M e).hom.app (DerivedCategory.Q.obj K) ≫
      M.mapDerivedCategoryFactors.hom.app K =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) := by
  simp only [mapDerivedCategoryTriangleIso, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [mapDerivedCategoryOriginalIso_fac]
  rw [mapDerivedCategoryCompIso_fac_assoc]
end Triangle
end CategoryTheory.Functor
