/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ChangeTargetUnit
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Postcomposition

/-! # Target-model transport of the original exact comparison -/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus
namespace CategoryTheory.Functor
universe u v u' v' dA dB₀ dB₁
variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
  [Abelian A] [Abelian B] [EnoughInjectives A]
  (hA : HasDerivedCategory.{dA} A)
  (hB₀ : HasDerivedCategory.{dB₀} B) (hB₁ : HasDerivedCategory.{dB₁} B)
  (F : A ⥤ B) [F.Additive] [F.PreservesHomology]

/-- The original inverse-unit exact comparison in explicitly specified native models. -/
abbrev rightDerivedFunctorPlusExactComparisonModel :
    (@DerivedCategory.Plus.Q _ _ _ hA) ⋙ (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hB₀ F _
      _) ≅ F.mapCochainComplexPlus ⋙ (@DerivedCategory.Plus.Q _ _ _ hB₀) := by
  letI := hA
  letI := hB₀
  exact F.rightDerivedFunctorPlusExactComparison

/-- Original exact descent commutes with canonical native target comparison. -/
@[reassoc]
theorem rightDerivedFunctorPlusChangeTarget_exact (K : CochainComplex.Plus A) :
    (canonicalEquivalence hB₀ hB₁).functor.map
        ((rightDerivedFunctorPlusExactComparisonModel hA hB₀ F).hom.app K) ≫
      (quotientCompCanonicalEquivalenceIso hB₀ hB₁).hom.app (F.mapCochainComplexPlus.obj K) =
    (rightDerivedFunctorPlusChangeTarget hA hB₀ hB₁ F).hom.app (((@DerivedCategory.Plus.Q _ _ _
      hA)).obj K) ≫
      (rightDerivedFunctorPlusExactComparisonModel hA hB₁ F).hom.app K := by
  let e₀ := rightDerivedFunctorPlusExactComparisonModel hA hB₀ F
  let e₁ := rightDerivedFunctorPlusExactComparisonModel hA hB₁ F
  have h := rightDerivedFunctorPlusChangeTarget_unit hA hB₀ hB₁ F K
  change (canonicalEquivalence hB₀ hB₁).functor.map (e₀.inv.app K) ≫ _ =
    (quotientCompCanonicalEquivalenceIso hB₀ hB₁).hom.app (F.mapCochainComplexPlus.obj K) ≫
      e₁.inv.app K at h
  apply (cancel_epi ((canonicalEquivalence hB₀ hB₁).functor.map (e₀.inv.app K))).mp
  rw [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp, ← Category.assoc, h, Category.assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Category.comp_id]

end CategoryTheory.Functor
