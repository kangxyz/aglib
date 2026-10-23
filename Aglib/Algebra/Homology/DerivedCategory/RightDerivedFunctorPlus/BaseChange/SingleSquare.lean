/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ExactSquare
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology

/-!
# Native single normalization for an exact derived square

The original termwise single maps and exact localization comparisons identify
an exact derived square on coefficient singles. A shared proposition keeps
specializations at large sheaf functors from re-expanding the original equation.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

universe uA vA wA uB vB wB uC vC wC uD vD wD

section SingleComplex
variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  (F : A ⥤ B) [F.Additive]

/-- The native termwise single comparison in the original plus category. -/
def Functor.mapCochainComplexPlusSingleIso (T : A) :
    F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus A 0).obj T) ≅
      (CochainComplex.singleFunctorPlus B 0).obj (F.obj T) :=
  (CochainComplex.plus B).isoMk
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app T)

variable [HasDerivedCategory.{wA} A] [EnoughInjectives A]
  [HasDerivedCategory.{wB} B] [F.PreservesHomology]

/-- The original exact-single comparison factors through the original exact unit inverse. -/
theorem Functor.rightDerivedFunctorPlusSingleIso_exactComparison (T : A) :
    (F.rightDerivedFunctorPlusSingleIso 0).hom.app T =
      F.rightDerivedFunctorPlusExactComparison.hom.app
        ((CochainComplex.singleFunctorPlus A 0).obj T) ≫
      DerivedCategory.Plus.Q.map (Functor.mapCochainComplexPlusSingleIso F T).hom := by
  let K := (CochainComplex.singleFunctorPlus A 0).obj T
  let : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have hu : F.rightDerivedFunctorPlusUnit.app K ≫
      F.rightDerivedFunctorPlusExactComparison.hom.app K = 𝟙 _ := by
    change (asIso F.rightDerivedFunctorPlusUnit).hom.app K ≫
      (asIso F.rightDerivedFunctorPlusUnit).inv.app K = 𝟙 _
    exact (asIso F.rightDerivedFunctorPlusUnit).hom_inv_id_app K
  apply (cancel_epi (F.rightDerivedFunctorPlusUnit.app K)).mp
  rw [← Category.assoc, hu, Category.id_comp]
  exact F.rightDerivedFunctorPlusSingleIso_unit 0 T

variable {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wD} D] [EnoughInjectives B]
  (H : B ⥤ D) [H.Additive] [H.PreservesHomology]

/-- Composition factorization over abstract functors avoids concrete sheaf reductions. -/
theorem Functor.rightDerivedFunctorPlusSingleIso_comp_exactComparison (T : A) :
    H.rightDerivedFunctorPlus.map ((F.rightDerivedFunctorPlusSingleIso 0).hom.app T) ≫
      (H.rightDerivedFunctorPlusSingleIso 0).hom.app (F.obj T) =
    H.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusExactComparison.hom.app
        ((CochainComplex.singleFunctorPlus A 0).obj T)) ≫
      H.rightDerivedFunctorPlusExactComparison.hom.app
        (F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus A 0).obj T)) ≫
      DerivedCategory.Plus.Q.map
        (H.mapCochainComplexPlus.map (Functor.mapCochainComplexPlusSingleIso F T).hom ≫
          (Functor.mapCochainComplexPlusSingleIso H (F.obj T)).hom) := by
  have hn := H.rightDerivedFunctorPlusExactComparison.hom.naturality
    (Functor.mapCochainComplexPlusSingleIso F T).hom
  change H.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map (Functor.mapCochainComplexPlusSingleIso F T).hom) ≫
      H.rightDerivedFunctorPlusExactComparison.hom.app _ =
    H.rightDerivedFunctorPlusExactComparison.hom.app _ ≫
      DerivedCategory.Plus.Q.map (H.mapCochainComplexPlus.map
        (Functor.mapCochainComplexPlusSingleIso F T).hom) at hn
  rw [Functor.rightDerivedFunctorPlusSingleIso_exactComparison,
    Functor.rightDerivedFunctorPlusSingleIso_exactComparison, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  simp only [Functor.map_comp]

end SingleComplex

section Square
variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (F : A ⥤ B) (H : B ⥤ D) (G : A ⥤ C) (V : C ⥤ D)
  [F.Additive] [H.Additive] [G.Additive] [V.Additive]
  (α : G ⋙ V ⟶ F ⋙ H)

/-- Compatibility on original complexes is native single-map naturality. -/
theorem TwoSquare.mapCochainComplexPlus_single (T : A) :
    (TwoSquare.mk G F V H α).mapCochainComplexPlus.app
        ((CochainComplex.singleFunctorPlus A 0).obj T) ≫
      H.mapCochainComplexPlus.map (Functor.mapCochainComplexPlusSingleIso F T).hom ≫
      (Functor.mapCochainComplexPlusSingleIso H (F.obj T)).hom =
    V.mapCochainComplexPlus.map (Functor.mapCochainComplexPlusSingleIso G T).hom ≫
      (Functor.mapCochainComplexPlusSingleIso V (G.obj T)).hom ≫
      (CochainComplex.singleFunctorPlus D 0).map (α.app T) := by
  apply ObjectProperty.hom_ext
  ext i
  by_cases hi : i = 0
  · subst i
    simp [TwoSquare.mapCochainComplexPlus, TwoSquare.mk, TwoSquare.natTrans,
      Functor.mapCochainComplexPlusCompIso,
      Functor.mapCochainComplexPlusSingleIso, NatTrans.mapCochainComplexPlus_app_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, CochainComplex.singleFunctorPlus,
      CochainComplex.singleFunctor, ObjectProperty.lift, HomologicalComplex.single]
  · exact (V.map_isZero (G.map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 T i hi))).eq_of_src _ _

variable [HasDerivedCategory.{wA} A] [EnoughInjectives A]
  [HasDerivedCategory.{wB} B] [EnoughInjectives B]
  [HasDerivedCategory.{wC} C] [EnoughInjectives C]
  [HasDerivedCategory.{wD} D]
  [F.PreservesHomology] [H.PreservesHomology] [G.PreservesHomology] [V.PreservesHomology]
  (αD : G.rightDerivedFunctorPlus ⋙ V.rightDerivedFunctorPlus ⟶
    F.rightDerivedFunctorPlus ⋙ H.rightDerivedFunctorPlus)

/-- Shared native-single equation keeps scheme specialization small. -/
def SingleComparisonSquareEquation (T : A) : Prop :=
  αD.app ((DerivedCategory.Plus.singleFunctor A 0).obj T) ≫
      H.rightDerivedFunctorPlus.map ((F.rightDerivedFunctorPlusSingleIso 0).hom.app T) ≫
      (H.rightDerivedFunctorPlusSingleIso 0).hom.app (F.obj T) =
    V.rightDerivedFunctorPlus.map ((G.rightDerivedFunctorPlusSingleIso 0).hom.app T) ≫
      (V.rightDerivedFunctorPlusSingleIso 0).hom.app (G.obj T) ≫
      (DerivedCategory.Plus.singleFunctor D 0).map (α.app T)

/-- A native exact square induces its original native single square. -/
theorem singleComparisonSquareEquation (T : A)
    (he : ExactComparisonSquareEquation F H G V
      (TwoSquare.mk G F V H α) (TwoSquare.mk _ _ _ _ αD)
      ((CochainComplex.singleFunctorPlus A 0).obj T)) :
    SingleComparisonSquareEquation F H G V α αD T := by
  dsimp only [ExactComparisonSquareEquation, TwoSquare.mk] at he
  dsimp only [SingleComparisonSquareEquation]
  change αD.app (DerivedCategory.Plus.Q.obj
      ((CochainComplex.singleFunctorPlus A 0).obj T)) ≫
      H.rightDerivedFunctorPlus.map ((F.rightDerivedFunctorPlusSingleIso 0).hom.app T) ≫
      (H.rightDerivedFunctorPlusSingleIso 0).hom.app (F.obj T) =
    V.rightDerivedFunctorPlus.map ((G.rightDerivedFunctorPlusSingleIso 0).hom.app T) ≫
      (V.rightDerivedFunctorPlusSingleIso 0).hom.app (G.obj T) ≫
      DerivedCategory.Plus.Q.map ((CochainComplex.singleFunctorPlus D 0).map (α.app T))
  have hC := congrArg DerivedCategory.Plus.Q.map
    (TwoSquare.mapCochainComplexPlus_single F H G V α T)
  simp only [Functor.map_comp] at hC
  rw [Functor.rightDerivedFunctorPlusSingleIso_comp_exactComparison F H T,
    reassoc_of% (Functor.rightDerivedFunctorPlusSingleIso_comp_exactComparison G V T)]
  rw [← reassoc_of% he]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun k =>
    V.rightDerivedFunctorPlus.map
        (G.rightDerivedFunctorPlusExactComparison.hom.app
          ((CochainComplex.singleFunctorPlus A 0).obj T)) ≫
      V.rightDerivedFunctorPlusExactComparison.hom.app
        (G.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus A 0).obj T)) ≫ k) hC

end Square
end CategoryTheory
