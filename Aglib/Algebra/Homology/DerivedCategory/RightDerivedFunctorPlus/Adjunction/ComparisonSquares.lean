/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction

/-! # The exact-left and original-right squares of derived composition -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Functor
universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B] [EnoughInjectives B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C) [F.Additive] [G.Additive] [H.Additive]

omit [EnoughInjectives B] in
@[simp]
theorem rightDerivedFunctorPlusExactComparison_inv_app [F.PreservesHomology]
    (K : CochainComplex.Plus A) :
    F.rightDerivedFunctorPlusExactComparison.inv.app K = F.rightDerivedFunctorPlusUnit.app K :=
  rfl

/-- The inverse exact comparisons cancel the original two-factor right-derived unit. -/
theorem rightDerivedFunctorPlusCompUnit_exactComparison
    [F.PreservesHomology] [G.PreservesHomology] (K : CochainComplex.Plus A) :
    (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K)) ≫
      (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusExactComparison.hom.app K) ≫
        G.rightDerivedFunctorPlusExactComparison.hom.app (F.mapCochainComplexPlus.obj K)) =
      𝟙 _ := by
  have hf := F.rightDerivedFunctorPlusExactComparison.inv_hom_id_app K
  have hg := G.rightDerivedFunctorPlusExactComparison.inv_hom_id_app
    (F.mapCochainComplexPlus.obj K)
  rw [rightDerivedFunctorPlusExactComparison_inv_app] at hf hg
  rw [Category.assoc, ← Category.assoc (G.rightDerivedFunctorPlus.map _),
    ← G.rightDerivedFunctorPlus.map_comp, hf]
  have hm := G.rightDerivedFunctorPlus.map_id
    ((F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).obj K)
  rw [hm]
  simpa only [Functor.comp_obj, Category.id_comp] using hg

/-- The transported native composition satisfies its exact-left comparison square. -/
theorem rightDerivedFunctorPlusCompIso_exactComparison_square
    [F.PreservesHomology] [G.PreservesHomology] [H.PreservesHomology]
    (e : H ≅ F ⋙ G) (K : CochainComplex.Plus A) :
    (H.rightDerivedFunctorPlusIso e ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).hom.app
          (DerivedCategory.Plus.Q.obj K) ≫
      (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusExactComparison.hom.app K) ≫
        G.rightDerivedFunctorPlusExactComparison.hom.app (F.mapCochainComplexPlus.obj K)) =
      H.rightDerivedFunctorPlusExactComparison.hom.app K ≫ DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus e ≪≫ mapCochainComplexPlusCompIso F G).hom.app K) := by
  have he : (NatIso.mapCochainComplexPlus e ≪≫ mapCochainComplexPlusCompIso F G).hom.app K =
      (NatIso.mapCochainComplexPlus e).hom.app K := by
    simp [mapCochainComplexPlusCompIso]
  rw [he]
  apply (cancel_epi (H.rightDerivedFunctorPlusExactComparison.inv.app K)).mp
  rw [rightDerivedFunctorPlusExactComparison_inv_app]
  have hu : H.rightDerivedFunctorPlusUnit.app K ≫
      (H.rightDerivedFunctorPlusIso e ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).hom.app
          (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map ((NatIso.mapCochainComplexPlus e).hom.app K) ≫
        (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
          G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K)) := by
    dsimp only [Iso.trans_hom, NatTrans.comp_app]
    rw [← Category.assoc, rightDerivedFunctorPlusIso_hom_app, Category.assoc,
      rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app]
  rw [← Category.assoc, hu, Category.assoc,
    rightDerivedFunctorPlusCompUnit_exactComparison, ← Category.assoc]
  have hh := H.rightDerivedFunctorPlusExactComparison.inv_hom_id_app K
  rw [rightDerivedFunctorPlusExactComparison_inv_app] at hh
  rw [hh, Category.id_comp]
  exact Category.comp_id (DerivedCategory.Plus.Q.map ((NatIso.mapCochainComplexPlus e).hom.app K))

/-- The inverse native injective comparison satisfies its original right-unit square. -/
theorem rightDerivedFunctorPlusCompIso_originalUnit_square
    [F.PreservesInjectiveObjects] (e : F ⋙ G ≅ H) (K : CochainComplex.Plus A) :
    (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K)) ≫
      (H.rightDerivedFunctorPlusIso e.symm ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G).inv.app
          (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
        (((mapCochainComplexPlusCompIso F G).symm ≪≫
          NatIso.mapCochainComplexPlus e).hom.app K) ≫ H.rightDerivedFunctorPlusUnit.app K := by
  have he : ((mapCochainComplexPlusCompIso F G).symm ≪≫
      NatIso.mapCochainComplexPlus e).hom.app K =
      (NatIso.mapCochainComplexPlus e).hom.app K := by
    simp only [Functor.comp_obj, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    exact Category.id_comp ((NatIso.mapCochainComplexPlus e).hom.app K)
  rw [he]
  let c := H.rightDerivedFunctorPlusIso e.symm ≪≫
    rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G
  have hu : H.rightDerivedFunctorPlusUnit.app K ≫ c.hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map ((NatIso.mapCochainComplexPlus e).inv.app K) ≫
        (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
          G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K)) := by
    dsimp only [c, Iso.trans_hom, NatTrans.comp_app]
    rw [← Category.assoc, rightDerivedFunctorPlusIso_hom_app, Category.assoc,
      rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app]
    have heinv : (NatIso.mapCochainComplexPlus e.symm).hom.app K =
        (NatIso.mapCochainComplexPlus e).inv.app K := by
      apply ObjectProperty.hom_ext
      ext n
      rfl
    rw [heinv]
  apply (cancel_mono (c.hom.app (DerivedCategory.Plus.Q.obj K))).mp
  change (_ ≫ c.inv.app _) ≫ c.hom.app _ = _
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Category.assoc, hu,
    ← Category.assoc, ← DerivedCategory.Plus.Q.map_comp,
    Iso.hom_inv_id_app]
  have hid := DerivedCategory.Plus.Q.map_id ((F ⋙ G).mapCochainComplexPlus.obj K)
  rw [hid]
  exact (Category.id_comp _).symm

end CategoryTheory.Functor
