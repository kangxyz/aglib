/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ChangeTargetCoherence
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ChangeTargetExact
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.UnitComparison
public import Aglib.CategoryTheory.Functor.TargetUnitSquare

/-! # Original-unit coherence of derived mates in independent target models -/

@[expose] public noncomputable section
open CategoryTheory.Functor DerivedCategory.Plus
namespace CategoryTheory
universe uA vA uB vB uC vC uD vD dA dB dC₀ dC₁ dD
variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C] [EnoughInjectives D]
  (hA : HasDerivedCategory.{dA} A) (hB : HasDerivedCategory.{dB} B)
  (hC₀ : HasDerivedCategory.{dC₀} C) (hC₁ : HasDerivedCategory.{dC₁} C)
  (hD : HasDerivedCategory.{dD} D)
  (G : A ⥤ C) (H : B ⥤ D) (R : B ⥤ A) (S : D ⥤ C)
  [G.Additive] [H.Additive] [R.Additive] [S.Additive]
  [G.PreservesHomology] [H.PreservesHomology]
  (b : R ⋙ G ⟶ H ⋙ S)

/-- The original complex-unit equation, retaining explicit native models and the actual map. -/
def DerivedTargetMateUnitEquation
    (β : (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hA R _ _) ⋙
      (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hC₀ G _ _) ⟶
      (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hD H _ _) ⋙
        (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hD hC₀ S _ _))
    (K : CochainComplex.Plus B) : Prop :=
  ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hC₀ G _ _)).map
      (((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hB hA R _ _)).app K) ≫
      β.app (((@DerivedCategory.Plus.Q _ _ _ hB)).obj K) ≫
      ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hD hC₀ S _ _)).map
        ((rightDerivedFunctorPlusExactComparisonModel hB hD H).hom.app K) =
    (rightDerivedFunctorPlusExactComparisonModel hA hC₀ G).hom.app
        (R.mapCochainComplexPlus.obj K) ≫
      ((@DerivedCategory.Plus.Q _ _ _ hC₀)).map (b.mapCochainComplexPlus.app K) ≫
      ((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hD hC₀ S _ _)).app
        (H.mapCochainComplexPlus.obj K)

omit [EnoughInjectives C] in
/-- Two maps satisfying the original complex-unit equations commute with canonical
native target transport. The source unit need not be invertible. -/
theorem derivedTargetMate_square
    (β₀ : (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hA R _ _) ⋙
      (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hC₀ G _ _) ⟶
      (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hD H _ _) ⋙
        (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hD hC₀ S _ _))
    (β₁ : (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hA R _ _) ⋙
      (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hC₁ G _ _) ⟶
      (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hD H _ _) ⋙
        (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hD hC₁ S _ _))
    (hu₀ : ∀ K, DerivedTargetMateUnitEquation hA hB hC₀ hD G H R S b β₀ K)
    (hu₁ : ∀ K, DerivedTargetMateUnitEquation hA hB hC₁ hD G H R S b β₁ K) :
    whiskerRight β₀ (canonicalEquivalence hC₀ hC₁).functor ≫
        (associator _ _ _).hom ≫
        whiskerLeft ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hD H _ _))
          (rightDerivedFunctorPlusChangeTarget hD hC₀ hC₁ S).hom =
      (associator _ _ _).hom ≫
        whiskerLeft ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hA R _ _))
          (rightDerivedFunctorPlusChangeTarget hA hC₀ hC₁ G).hom ≫ β₁ := by
  let : ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hA R _ _) ⋙
      (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hC₀ G _ _)).IsRightDerivedFunctor
      (whiskerRight ((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hB hA R _ _))
        ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hC₀ G _ _)) ≫ (associator _ _ _).hom)
      (CochainComplex.Plus.quasiIso B) := by
    let := hB
    let := hA
    exact R.isRightDerivedFunctor_rightDerivedFunctorPlus_postcomp _
  apply rightDerivedTarget_ext ((@DerivedCategory.Plus.Q _ _ _ hB)) (CochainComplex.Plus.quasiIso B)
    (canonicalEquivalence hC₀ hC₁) _
    (whiskerRight ((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hB hA R _ _))
      ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hC₀ G _ _)) ≫ (associator _ _ _).hom)
  intro K
  dsimp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, associator_hom_app]
  simp only [Category.comp_id, Category.id_comp]
  apply targetUnitSquare
    ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hC₀ G _ _))
      ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hC₁ G _ _))
    ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hD hC₀ S _ _))
      ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hD hC₁ S _ _))
    (canonicalEquivalence hC₀ hC₁).functor
    (rightDerivedFunctorPlusChangeTarget hA hC₀ hC₁ G)
    (rightDerivedFunctorPlusChangeTarget hD hC₀ hC₁ S)
    (((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hB hA R _ _)).app K)
    ((rightDerivedFunctorPlusExactComparisonModel hB hD H).app K)
    (β₀.app (((@DerivedCategory.Plus.Q _ _ _ hB)).obj K)) (β₁.app (((@DerivedCategory.Plus.Q _ _ _
      hB)).obj K))
    ((rightDerivedFunctorPlusExactComparisonModel hA hC₀ G).hom.app
      (R.mapCochainComplexPlus.obj K))
    ((rightDerivedFunctorPlusExactComparisonModel hA hC₁ G).hom.app
      (R.mapCochainComplexPlus.obj K))
    ((quotientCompCanonicalEquivalenceIso hC₀ hC₁).hom.app
      (G.mapCochainComplexPlus.obj (R.mapCochainComplexPlus.obj K)))
    (((@DerivedCategory.Plus.Q _ _ _ hC₀)).map (b.mapCochainComplexPlus.app K) ≫
      ((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hD hC₀ S _ _)).app
        (H.mapCochainComplexPlus.obj K))
    (((@DerivedCategory.Plus.Q _ _ _ hC₁)).map (b.mapCochainComplexPlus.app K) ≫
      ((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hD hC₁ S _ _)).app
        (H.mapCochainComplexPlus.obj K))
    (hu₀ K) (hu₁ K)
    (rightDerivedFunctorPlusChangeTarget_exact hA hC₀ hC₁ G
      (R.mapCochainComplexPlus.obj K))
  rw [Functor.map_comp, Category.assoc]
  simp only [Functor.comp_obj]
  rw [rightDerivedFunctorPlusChangeTarget_unit hD hC₀ hC₁ S
    (H.mapCochainComplexPlus.obj K)]
  have hn := congrArg
    (fun z => z ≫ ((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ hD hC₁ S _ _)).app
      (H.mapCochainComplexPlus.obj K))
    ((quotientCompCanonicalEquivalenceIso hC₀ hC₁).hom.naturality (b.mapCochainComplexPlus.app K))
  simp only [Functor.comp_obj, Functor.comp_map, Category.assoc] at hn ⊢
  convert hn using 1 <;> rfl

end CategoryTheory
