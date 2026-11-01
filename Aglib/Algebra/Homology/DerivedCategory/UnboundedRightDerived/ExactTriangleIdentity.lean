/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactTriangleCoherence

/-! # Identity coherence of the original localized exact triangle -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
universe uA vA wA uB vB wB
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  (F : A ⥤ B) (J : B ⥤ B) [F.Additive] [J.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]

/-- The specified original identity comparison on all complexes. -/
theorem mapDerivedCategoryOriginalIdIso_fac (d : J ≅ 𝟭 B) (K : CochainComplex B ℤ) :
    (mapDerivedCategoryOriginalIso J (𝟭 B) d ≪≫ mapDerivedCategoryIdIso B).hom.app
        (DerivedCategory.Q.obj K) =
      J.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex d (.up ℤ)).hom.app K) := by
  have hi : (mapHomologicalComplexIdIso B (.up ℤ)).hom.app K = 𝟙 K := by
    ext n
    rfl
  simp only [Iso.trans_hom, NatTrans.comp_app, mapDerivedCategoryIdIso_hom_app, hi]
  rw [mapDerivedCategoryOriginalIso_fac_assoc]
  have hQ := (DerivedCategory.Q (C := B)).map_id K
  exact (congrArg (fun z => J.mapDerivedCategoryFactors.hom.app K ≫
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex d (.up ℤ)).hom.app K) ≫ z) hQ).trans
      (congrArg (fun z => J.mapDerivedCategoryFactors.hom.app K ≫ z)
        (Category.comp_id _))

/-- Localization preserves the original right-unit triangle. -/
theorem mapDerivedCategoryTriangleIso_id
    (σ : F ⋙ J ≅ F) (d : J ≅ 𝟭 B)
    (hc : σ = isoWhiskerLeft F d ≪≫ rightUnitor F) :
    mapDerivedCategoryTriangleIso F J F σ =
      isoWhiskerLeft F.mapDerivedCategory
          (mapDerivedCategoryOriginalIso J (𝟭 B) d ≪≫ mapDerivedCategoryIdIso B) ≪≫
        rightUnitor F.mapDerivedCategory := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app K)).mp
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app,
    rightUnitor_hom_app]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  simp only [Category.comp_id]
  rw [mapDerivedCategoryTriangleIso_fac]
  let dD := mapDerivedCategoryOriginalIso J (𝟭 B) d ≪≫ mapDerivedCategoryIdIso B
  have hn := dD.hom.naturality (F.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.id_map, Functor.comp_obj] at hn
  dsimp only [dD, Iso.trans_hom, NatTrans.comp_app] at hn
  rw [← hn]
  have hi := mapDerivedCategoryOriginalIdIso_fac J d
    ((F.mapHomologicalComplex (.up ℤ)).obj K)
  dsimp only [Iso.trans_hom, NatTrans.comp_app] at hi
  rw [hi]
  congr 2
  congr 1
  subst σ
  ext n
  simp [NatIso.mapHomologicalComplex]
end CategoryTheory.Functor
