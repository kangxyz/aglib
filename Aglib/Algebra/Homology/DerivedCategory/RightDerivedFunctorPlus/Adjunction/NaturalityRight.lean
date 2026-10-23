/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Naturality

/-! # Naturality of the installed derived composition comparison -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃
namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B] [EnoughInjectives B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  (F : A ⥤ B) [F.Additive]
  {G G' : B ⥤ C} [G.Additive] [G'.Additive]


/-- Naturality in the second factor, for the exact-second-factor comparison. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesHomology_naturality_right
    [G.PreservesHomology] [G'.PreservesHomology] (e : G ≅ G') :
    (F ⋙ G).rightDerivedFunctorPlusIso (isoWhiskerLeft F e) ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesHomology F G' =
      rightDerivedFunctorPlusCompIsoOfPreservesHomology F G ≪≫
        isoWhiskerLeft F.rightDerivedFunctorPlus (G.rightDerivedFunctorPlusIso e) := by
  apply Iso.ext
  apply (F ⋙ G).rightDerivedFunctorPlus.rightDerived_ext (F ⋙ G).rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso A)
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, whiskerLeft_app, Iso.trans_hom, isoWhiskerLeft_hom]
  rw [← Category.assoc, rightDerivedFunctorPlusIso_hom_app, Category.assoc,
    rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app]
  conv_rhs =>
    rw [← Category.assoc, rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app,
      Category.assoc]
  have hm : (NatIso.mapCochainComplexPlus (isoWhiskerLeft F e)).hom.app K =
      (NatIso.mapCochainComplexPlus e).hom.app (F.mapCochainComplexPlus.obj K) := by
    apply ObjectProperty.hom_ext
    ext n
    rfl
  rw [hm, ← Category.assoc, ← rightDerivedFunctorPlusIso_hom_app, Category.assoc]
  simpa only [comp_obj] using congrArg
    (fun t => G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫ t)
    ((G.rightDerivedFunctorPlusIso e).hom.naturality (F.rightDerivedFunctorPlusUnit.app K)).symm

/-- Naturality in the second factor, for the injective-preserving-first-factor comparison. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesInjectives_naturality_right
    [F.PreservesInjectiveObjects] (e : G ≅ G') :
    (F ⋙ G).rightDerivedFunctorPlusIso (isoWhiskerLeft F e) ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G' =
      rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G ≪≫
        isoWhiskerLeft F.rightDerivedFunctorPlus (G.rightDerivedFunctorPlusIso e) := by
  apply Iso.ext
  apply (F ⋙ G).rightDerivedFunctorPlus.rightDerived_ext (F ⋙ G).rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso A)
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, whiskerLeft_app, Iso.trans_hom, isoWhiskerLeft_hom]
  rw [← Category.assoc, rightDerivedFunctorPlusIso_hom_app, Category.assoc,
    rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app]
  conv_rhs =>
    rw [← Category.assoc, rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app,
      Category.assoc]
  have hm : (NatIso.mapCochainComplexPlus (isoWhiskerLeft F e)).hom.app K =
      (NatIso.mapCochainComplexPlus e).hom.app (F.mapCochainComplexPlus.obj K) := by
    apply ObjectProperty.hom_ext
    ext n
    rfl
  rw [hm, ← Category.assoc, ← rightDerivedFunctorPlusIso_hom_app, Category.assoc]
  simpa only [comp_obj] using congrArg
    (fun t => G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫ t)
    ((G.rightDerivedFunctorPlusIso e).hom.naturality (F.rightDerivedFunctorPlusUnit.app K)).symm

end CategoryTheory.Functor
