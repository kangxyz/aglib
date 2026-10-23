/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SingleSquare
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.IdentityConjugacy

/-! # Composition and identity coherence of the original exact-single comparison -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Functor
universe uA vA wA uB vB wB uC vC wC
variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {C : Type uC} [Category.{vC} C] [Abelian C]

/-- Original single-complex comparisons respect a specified composition comparison. -/
theorem mapCochainComplexPlusSingleIso_comp
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive] (e : H ≅ F ⋙ G) (M : A) :
    (NatIso.mapCochainComplexPlus e ≪≫ mapCochainComplexPlusCompIso F G).hom.app
        ((CochainComplex.singleFunctorPlus A 0).obj M) ≫
      G.mapCochainComplexPlus.map (F.mapCochainComplexPlusSingleIso M).hom ≫
      (G.mapCochainComplexPlusSingleIso (F.obj M)).hom =
    (H.mapCochainComplexPlusSingleIso M).hom ≫
      (CochainComplex.singleFunctorPlus C 0).map (e.hom.app M) := by
  apply ObjectProperty.hom_ext
  ext i
  by_cases hi : i = 0
  · subst i
    simp [mapCochainComplexPlusCompIso, mapCochainComplexPlusSingleIso,
      NatIso.mapCochainComplexPlus,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      CochainComplex.singleFunctorPlus, CochainComplex.singleFunctor,
      ObjectProperty.lift, HomologicalComplex.single]
  · exact (H.map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)).eq_of_src _ _

/-- Original single-complex comparisons respect a specified identity comparison. -/
theorem mapCochainComplexPlusSingleIso_id
    (F : A ⥤ A) [F.Additive] (e : F ≅ 𝟭 A) (M : A) :
    (NatIso.mapCochainComplexPlus e ≪≫ mapCochainComplexPlusIdIso A).hom.app
        ((CochainComplex.singleFunctorPlus A 0).obj M) =
      (F.mapCochainComplexPlusSingleIso M).hom ≫
        (CochainComplex.singleFunctorPlus A 0).map (e.hom.app M) := by
  apply ObjectProperty.hom_ext
  ext i
  by_cases hi : i = 0
  · subst i
    simp [mapCochainComplexPlusIdIso, mapCochainComplexPlusSingleIso,
      NatIso.mapCochainComplexPlus,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      CochainComplex.singleFunctorPlus, CochainComplex.singleFunctor,
      ObjectProperty.lift, HomologicalComplex.single]
  · exact (F.map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)).eq_of_src _ _

variable [HasDerivedCategory.{wA} A] [EnoughInjectives A]
  [HasDerivedCategory.{wB} B] [EnoughInjectives B] [HasDerivedCategory.{wC} C]

/-- The installed exact-single comparisons respect actual transported composition. -/
theorem rightDerivedFunctorPlusSingleIso_comp
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [F.PreservesHomology] [G.PreservesHomology] [H.PreservesHomology]
    (e : H ≅ F ⋙ G) (M : A) :
    (H.rightDerivedFunctorPlusIso e ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).hom.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj M) ≫
      G.rightDerivedFunctorPlus.map ((F.rightDerivedFunctorPlusSingleIso 0).hom.app M) ≫
      (G.rightDerivedFunctorPlusSingleIso 0).hom.app (F.obj M) =
    (H.rightDerivedFunctorPlusSingleIso 0).hom.app M ≫
      (DerivedCategory.Plus.singleFunctor C 0).map (e.hom.app M) := by
  let K := (CochainComplex.singleFunctorPlus A 0).obj M
  have he := rightDerivedFunctorPlusCompIso_exactComparison_square F G H e K
  have hc := congrArg DerivedCategory.Plus.Q.map
    (mapCochainComplexPlusSingleIso_comp F G H e M)
  change (H.rightDerivedFunctorPlusIso e ≪≫
      rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).hom.app
        (DerivedCategory.Plus.Q.obj K) ≫
      G.rightDerivedFunctorPlus.map ((F.rightDerivedFunctorPlusSingleIso 0).hom.app M) ≫
      (G.rightDerivedFunctorPlusSingleIso 0).hom.app (F.obj M) =
    (H.rightDerivedFunctorPlusSingleIso 0).hom.app M ≫
      DerivedCategory.Plus.Q.map ((CochainComplex.singleFunctorPlus C 0).map (e.hom.app M))
  rw [rightDerivedFunctorPlusSingleIso_comp_exactComparison,
    rightDerivedFunctorPlusSingleIso_exactComparison]
  simp only [Category.assoc]
  rw [reassoc_of% he]
  simp only [Functor.map_comp] at hc
  simpa only [K, Functor.map_comp, Category.assoc] using
    congrArg (fun z => H.rightDerivedFunctorPlusExactComparison.hom.app K ≫ z) hc

omit [EnoughInjectives B] in
/-- The installed exact-single comparison respects an actual transported identity. -/
theorem rightDerivedFunctorPlusSingleIso_id
    (F : A ⥤ A) [F.Additive] [F.PreservesHomology]
    (e : F ≅ 𝟭 A) (M : A) :
    (F.rightDerivedFunctorPlusIso e ≪≫ rightDerivedFunctorPlusIdIso A).hom.app
        ((DerivedCategory.Plus.singleFunctor A 0).obj M) =
      (F.rightDerivedFunctorPlusSingleIso 0).hom.app M ≫
        (DerivedCategory.Plus.singleFunctor A 0).map (e.hom.app M) := by
  change (F.rightDerivedFunctorPlusIso e ≪≫ rightDerivedFunctorPlusIdIso A).hom.app
      (DerivedCategory.Plus.Q.obj ((CochainComplex.singleFunctorPlus A 0).obj M)) =
    (F.rightDerivedFunctorPlusSingleIso 0).hom.app M ≫
      DerivedCategory.Plus.Q.map ((CochainComplex.singleFunctorPlus A 0).map (e.hom.app M))
  rw [rightDerivedFunctorPlusIso_id_exactComparison,
    mapCochainComplexPlusSingleIso_id, rightDerivedFunctorPlusSingleIso_exactComparison,
    Functor.map_comp, Category.assoc]

end CategoryTheory.Functor
