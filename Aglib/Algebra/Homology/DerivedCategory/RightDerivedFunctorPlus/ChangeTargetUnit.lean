/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.ModelComparisonCoherence
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-! # Target-only transport of the original right-derived unit

The source localization is fixed. Its original derived unit, postcomposed with
the specified target equivalence, determines the comparison uniquely. No
auxiliary source-model self-comparison or middle-model wrapper is introduced.
-/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus
namespace CategoryTheory.Functor

section Localization
variable {C D H₀ H₁ : Type*}
  [Category* C] [Category* D] [Category* H₀] [Category* H₁]
  (L : C ⥤ D) (T : H₀ ≌ H₁) {F : C ⥤ H₀}
  (R : D ⥤ H₀) (α : F ⟶ L ⋙ R)

/-- Ordinary whiskering transports the original unit to the specified target. -/
def rightDerivedTargetUnit : F ⋙ T.functor ⟶ L ⋙ (R ⋙ T.functor) :=
  whiskerRight α T.functor ≫ (associator _ _ _).hom

instance rightDerivedTargetUnit_isRightDerivedFunctor (W : MorphismProperty C)
    [L.IsLocalization W] [R.IsRightDerivedFunctor α W] :
    (R ⋙ T.functor).IsRightDerivedFunctor (rightDerivedTargetUnit L T R α) W := by
  change (R ⋙ T.functor).IsRightDerivedFunctor
    (whiskerRight α T.functor ≫ (associator _ _ _).hom) W
  infer_instance

end Localization

universe u v u' v' dA dB₀ dB₁
variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
  [Abelian A] [Abelian B] [EnoughInjectives A]
  (hA : HasDerivedCategory.{dA} A)
  (hB₀ : HasDerivedCategory.{dB₀} B) (hB₁ : HasDerivedCategory.{dB₁} B)
  (F : A ⥤ B) [F.Additive]

/-- The unit-normalized target comparison of the two original native derived functors. -/
def rightDerivedFunctorPlusChangeTarget :
    @Functor.rightDerivedFunctorPlus A B _ _ _ _ hA hB₀ F _ _ ⋙
        (canonicalEquivalence hB₀ hB₁).functor ≅
      @Functor.rightDerivedFunctorPlus A B _ _ _ _ hA hB₁ F _ _ :=
  rightDerivedNatIso _ _
    (rightDerivedTargetUnit (@DerivedCategory.Plus.Q A _ _ hA)
      (canonicalEquivalence hB₀ hB₁) _
      (@Functor.rightDerivedFunctorPlusUnit A B _ _ _ _ hA hB₀ F _ _))
    (@Functor.rightDerivedFunctorPlusUnit A B _ _ _ _ hA hB₁ F _ _)
    (CochainComplex.Plus.quasiIso A)
    (associator _ _ _ ≪≫ isoWhiskerLeft F.mapCochainComplexPlus
      (quotientCompCanonicalEquivalenceIso hB₀ hB₁))

/-- The comparison preserves both original units and the actual quotient comparison. -/
@[reassoc]
theorem rightDerivedFunctorPlusChangeTarget_unit (K : CochainComplex.Plus A) :
    (canonicalEquivalence hB₀ hB₁).functor.map
        ((@Functor.rightDerivedFunctorPlusUnit A B _ _ _ _ hA hB₀ F _ _).app K) ≫
      (rightDerivedFunctorPlusChangeTarget hA hB₀ hB₁ F).hom.app
        ((@DerivedCategory.Plus.Q A _ _ hA).obj K) =
    (quotientCompCanonicalEquivalenceIso hB₀ hB₁).hom.app (F.mapCochainComplexPlus.obj K) ≫
      (@Functor.rightDerivedFunctorPlusUnit A B _ _ _ _ hA hB₁ F _ _).app K := by
  have h := congr_app (rightDerivedNatTrans_fac _ _
    (rightDerivedTargetUnit (@DerivedCategory.Plus.Q A _ _ hA)
      (canonicalEquivalence hB₀ hB₁) _
      (@Functor.rightDerivedFunctorPlusUnit A B _ _ _ _ hA hB₀ F _ _))
    (@Functor.rightDerivedFunctorPlusUnit A B _ _ _ _ hA hB₁ F _ _)
    (CochainComplex.Plus.quasiIso A)
    (associator _ _ _ ≪≫ isoWhiskerLeft F.mapCochainComplexPlus
      (quotientCompCanonicalEquivalenceIso hB₀ hB₁)).hom) K
  simpa only [rightDerivedFunctorPlusChangeTarget, rightDerivedTargetUnit,
    rightDerivedNatIso_hom,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, associator_hom_app,
    Iso.trans_hom, isoWhiskerLeft_hom, Category.id_comp, Category.comp_id] using h

end CategoryTheory.Functor
