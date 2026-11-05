/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.NaturalTransformation
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Comparison.ThreeFactor

/-! # Coefficient naturality of the original derived composition comparison

The installed comparison commutes with arbitrary coefficient transformations
in either factor. Neither the transformation nor the comparison is assumed
invertible. This retains the original composite-unit normalization.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace CategoryTheory.Functor
universe uA vA wA uB vB wB uC vC wC
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]

/-- Component form of the original whole comparison unit. -/
theorem rightDerivedFunctorPlusCompComparison_unit_app
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (K : CochainComplex.Plus A) :
    (F ⋙ G).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusCompComparison F G).app (DerivedCategory.Plus.Q.obj K) =
      G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) := by
  simpa only [NatTrans.comp_app, whiskerLeft_app, rightDerivedFunctorPlusCompUnit_app] using
    NatTrans.congr_app (rightDerivedFunctorPlusCompComparison_unit F G) K

/-- Naturality in the original first coefficient functor for arbitrary transformations. -/
theorem rightDerivedFunctorPlusCompComparison_naturality_left
    {F F' : A ⥤ B} [F.Additive] [F'.Additive]
    (G : B ⥤ C) [G.Additive] (α : F ⟶ F') :
    (F ⋙ G).rightDerivedFunctorPlusNatTrans (whiskerRight α G) ≫
        rightDerivedFunctorPlusCompComparison F' G =
      rightDerivedFunctorPlusCompComparison F G ≫
        whiskerRight (F.rightDerivedFunctorPlusNatTrans α) G.rightDerivedFunctorPlus := by
  apply (F ⋙ G).rightDerivedFunctorPlus.rightDerived_ext (F ⋙ G).rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso A)
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [← Category.assoc, rightDerivedFunctorPlusNatTrans_app, Category.assoc,
    rightDerivedFunctorPlusCompComparison_unit_app]
  conv_rhs =>
    rw [← Category.assoc, rightDerivedFunctorPlusCompComparison_unit_app,
      Category.assoc, ← G.rightDerivedFunctorPlus.map_comp,
      rightDerivedFunctorPlusNatTrans_app, G.rightDerivedFunctorPlus.map_comp,
      ← Category.assoc]
  have hmap : (NatTrans.mapCochainComplexPlus (whiskerRight α G)).app K =
      G.mapCochainComplexPlus.map ((NatTrans.mapCochainComplexPlus α).app K) := by
    apply ObjectProperty.hom_ext
    ext n
    rfl
  rw [hmap]
  simpa only [Category.assoc, comp_obj, comp_map] using congrArg
    (fun t => t ≫ G.rightDerivedFunctorPlus.map (F'.rightDerivedFunctorPlusUnit.app K))
    (G.rightDerivedFunctorPlusUnit.naturality
      ((NatTrans.mapCochainComplexPlus α).app K))

/-- Naturality in the original second coefficient functor for arbitrary transformations. -/
theorem rightDerivedFunctorPlusCompComparison_naturality_right
    (F : A ⥤ B) [F.Additive] {G G' : B ⥤ C} [G.Additive] [G'.Additive]
    (α : G ⟶ G') :
    (F ⋙ G).rightDerivedFunctorPlusNatTrans (whiskerLeft F α) ≫
        rightDerivedFunctorPlusCompComparison F G' =
      rightDerivedFunctorPlusCompComparison F G ≫
        whiskerLeft F.rightDerivedFunctorPlus (G.rightDerivedFunctorPlusNatTrans α) := by
  apply (F ⋙ G).rightDerivedFunctorPlus.rightDerived_ext (F ⋙ G).rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso A)
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, whiskerLeft_app]
  rw [← Category.assoc, rightDerivedFunctorPlusNatTrans_app, Category.assoc,
    rightDerivedFunctorPlusCompComparison_unit_app]
  conv_rhs =>
    rw [← Category.assoc, rightDerivedFunctorPlusCompComparison_unit_app, Category.assoc]
  have hm : (NatTrans.mapCochainComplexPlus (whiskerLeft F α)).app K =
      (NatTrans.mapCochainComplexPlus α).app (F.mapCochainComplexPlus.obj K) := by
    apply ObjectProperty.hom_ext
    ext n
    rfl
  rw [hm, ← Category.assoc, ← rightDerivedFunctorPlusNatTrans_app, Category.assoc]
  simpa only [comp_obj] using congrArg
    (fun t => G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫ t)
    ((G.rightDerivedFunctorPlusNatTrans α).naturality (F.rightDerivedFunctorPlusUnit.app K)).symm

end CategoryTheory.Functor
