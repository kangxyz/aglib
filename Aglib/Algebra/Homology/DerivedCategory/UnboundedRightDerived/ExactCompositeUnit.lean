/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactCompositeCoherence

/-! # Original normalized units for exact unbounded compositors -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
universe uA vA wA uB vB wB
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

section Right
variable (F : A ⥤ B) (J : B ⥤ B) (P : A ⥤ B)
  [F.Additive] [J.Additive] [P.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]

/-- Localization preserves a specified compositor normalized at its right identity. -/
theorem mapDerivedCategoryCompositeIso_right_unit
    (c : P ≅ F ⋙ J) (d : J ≅ 𝟭 B) (e : P ≅ F)
    (hc : c ≪≫ isoWhiskerLeft F d ≪≫ rightUnitor F = e) :
    mapDerivedCategoryCompositeIso F J P c ≪≫
        isoWhiskerLeft F.mapDerivedCategory
          (mapDerivedCategoryOriginalIso J (𝟭 B) d ≪≫ mapDerivedCategoryIdIso B) ≪≫
        rightUnitor F.mapDerivedCategory = mapDerivedCategoryOriginalIso P F e := by
  have hσ : c.symm ≪≫ e = isoWhiskerLeft F d ≪≫ rightUnitor F := by
    rw [← hc]
    simp
  have ht := mapDerivedCategoryTriangleIso_id F J (c.symm ≪≫ e) d hσ
  simp only [mapDerivedCategoryTriangleIso, mapDerivedCategoryOriginalIso_trans,
    mapDerivedCategoryOriginalIso_symm] at ht
  have hh := congrArg (fun z => mapDerivedCategoryCompositeIso F J P c ≪≫ z) ht
  simpa only [mapDerivedCategoryCompositeIso, Iso.trans_assoc,
    Iso.symm_self_id_assoc, Iso.self_symm_id_assoc] using hh.symm
end Right

section Left
variable (J : A ⥤ A) (F : A ⥤ B)
  [F.Additive] [J.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]

/-- Localization preserves the original left-unit triangle. -/
theorem mapDerivedCategoryTriangleIso_left_id
    (σ : J ⋙ F ≅ F) (d : J ≅ 𝟭 A)
    (hc : σ = isoWhiskerRight d F ≪≫ leftUnitor F) :
    mapDerivedCategoryTriangleIso J F F σ =
      isoWhiskerRight (mapDerivedCategoryOriginalIso J (𝟭 A) d ≪≫
          mapDerivedCategoryIdIso A) F.mapDerivedCategory ≪≫
        leftUnitor F.mapDerivedCategory := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app K)).mp
  simp only [Iso.trans_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerRight_app,
    leftUnitor_hom_app]
  erw [Category.comp_id]
  rw [mapDerivedCategoryTriangleIso_fac]
  have hi := mapDerivedCategoryOriginalIdIso_fac J d K
  dsimp only [Iso.trans_hom, NatTrans.comp_app] at hi
  rw [hi]
  rw [F.mapDerivedCategory.map_comp]
  have hn := F.mapDerivedCategoryFactors.hom.naturality
    ((NatIso.mapHomologicalComplex d (.up ℤ)).hom.app K)
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc]
  erw [hn]
  congr 1
  subst σ
  congr 1
  congr 1
  ext n
  simp [NatIso.mapHomologicalComplex]

variable (P : A ⥤ B) [P.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]

/-- Localization preserves a specified compositor normalized at its left identity. -/
theorem mapDerivedCategoryCompositeIso_left_unit
    (c : P ≅ J ⋙ F) (d : J ≅ 𝟭 A) (e : P ≅ F)
    (hc : c ≪≫ isoWhiskerRight d F ≪≫ leftUnitor F = e) :
    mapDerivedCategoryCompositeIso J F P c ≪≫
        isoWhiskerRight (mapDerivedCategoryOriginalIso J (𝟭 A) d ≪≫
          mapDerivedCategoryIdIso A) F.mapDerivedCategory ≪≫
        leftUnitor F.mapDerivedCategory = mapDerivedCategoryOriginalIso P F e := by
  have hσ : c.symm ≪≫ e = isoWhiskerRight d F ≪≫ leftUnitor F := by
    rw [← hc]
    simp
  have ht := mapDerivedCategoryTriangleIso_left_id J F (c.symm ≪≫ e) d hσ
  simp only [mapDerivedCategoryTriangleIso, mapDerivedCategoryOriginalIso_trans,
    mapDerivedCategoryOriginalIso_symm] at ht
  have hh := congrArg (fun z => mapDerivedCategoryCompositeIso J F P c ≪≫ z) ht
  simpa only [mapDerivedCategoryCompositeIso, Iso.trans_assoc,
    Iso.symm_self_id_assoc, Iso.self_symm_id_assoc] using hh.symm
end Left
end CategoryTheory.Functor
