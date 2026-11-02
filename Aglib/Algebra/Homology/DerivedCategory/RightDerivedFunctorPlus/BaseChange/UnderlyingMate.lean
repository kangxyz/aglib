/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Comparison.ThreeFactor
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.OriginalUnitUniqueness
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.PullbackCoherence
public import Aglib.CategoryTheory.Adjunction.Mates.Coherence

/-! # Original three-factor comparisons are the original derived mates

Exact horizontal functors and exact left adjoints preserve the original
comparison square. The canonical three-factor right comparison satisfies its
original unit equation and is therefore the mate of the specified inverse
comparison. Only exact horizontal units are cancelled; the right-adjoint units
need not be invertible. Each of the four actual categories keeps one independent
derived realization.
-/

@[expose] public noncomputable section

open CategoryTheory.Functor

namespace CategoryTheory

universe uA vA wA uB vB wB uC vC wC uD vD wD

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  [EnoughInjectives D]
  (G : A ⥤ C) (H : B ⥤ D) [G.Additive] [H.Additive]
  [G.PreservesHomology] [H.PreservesHomology]

section Direct

variable (R₁ : B ⥤ A) (R₂ : D ⥤ C) [R₁.Additive] [R₂.Additive]
  [IsIso (rightDerivedFunctorPlusCompComparison R₁ G)]
  [IsIso (rightDerivedFunctorPlusCompComparison H R₂)]

omit [EnoughInjectives C] in
/-- The original three-factor comparison satisfies the normalized exact-horizontal unit law. -/
theorem threeFactorComparison_originalUnit (e : R₁ ⋙ G ≅ H ⋙ R₂)
    (K : CochainComplex.Plus B) :
    G.rightDerivedFunctorPlus.map (R₁.rightDerivedFunctorPlusUnit.app K) ≫
      (rightDerivedFunctorPlusThreeFactorIso R₁ G H R₂ e).hom.app
        (DerivedCategory.Plus.Q.obj K) ≫
      R₂.rightDerivedFunctorPlus.map (H.rightDerivedFunctorPlusExactComparison.hom.app K) =
    G.rightDerivedFunctorPlusExactComparison.hom.app (R₁.mapCochainComplexPlus.obj K) ≫
      DerivedCategory.Plus.Q.map ((NatIso.mapCochainComplexPlus e).hom.app K) ≫
      R₂.rightDerivedFunctorPlusUnit.app (H.mapCochainComplexPlus.obj K) := by
  refine exchangeCoherence_rotate_start
    (G.rightDerivedFunctorPlusUnit.app (R₁.mapCochainComplexPlus.obj K))
    (G.rightDerivedFunctorPlusExactComparison.hom.app (R₁.mapCochainComplexPlus.obj K))
    (G.rightDerivedFunctorPlus.map (R₁.rightDerivedFunctorPlusUnit.app K))
    ((rightDerivedFunctorPlusThreeFactorIso R₁ G H R₂ e).hom.app
      (DerivedCategory.Plus.Q.obj K))
    (DerivedCategory.Plus.Q.map ((NatIso.mapCochainComplexPlus e).hom.app K) ≫
      R₂.rightDerivedFunctorPlusUnit.app (H.mapCochainComplexPlus.obj K))
    (R₂.rightDerivedFunctorPlus.map (H.rightDerivedFunctorPlusUnit.app K))
    (R₂.rightDerivedFunctorPlus.map (H.rightDerivedFunctorPlusExactComparison.hom.app K))
    ?_ ?_ ?_
  · exact G.rightDerivedFunctorPlusExactComparison.hom_inv_id_app
      (R₁.mapCochainComplexPlus.obj K)
  · exact (R₂.rightDerivedFunctorPlus.mapIso
      (H.rightDerivedFunctorPlusExactComparison.app K)).inv_hom_id
  · simpa only [rightDerivedFunctorPlusCompUnit_app, Category.assoc] using
      rightDerivedFunctorPlusThreeFactorIso_unit_app R₁ G H R₂ e K

end Direct

section Inverse

variable (L₁ : A ⥤ B) (L₂ : C ⥤ D) [L₁.Additive] [L₂.Additive]
  [L₁.PreservesHomology] [L₂.PreservesHomology]

omit [EnoughInjectives D] in
local instance underlyingInverseSourceComparisonIsIso :
    IsIso (rightDerivedFunctorPlusCompComparison L₁ H) :=
  isIso_rightDerivedFunctorPlusCompComparison_of_preservesHomology _ _

omit [EnoughInjectives D] in
local instance underlyingInverseTargetComparisonIsIso :
    IsIso (rightDerivedFunctorPlusCompComparison G L₂) :=
  isIso_rightDerivedFunctorPlusCompComparison_of_preservesHomology _ _

omit [EnoughInjectives D] in
/-- The original inverse three-factor comparison preserves the actual exact complex square. -/
theorem threeFactorInverse_exactComparison (e : L₁ ⋙ H ≅ G ⋙ L₂)
    (K : CochainComplex.Plus A) :
    ExactComparisonSquareEquation L₁ H G L₂ (TwoSquare.mk _ _ _ _ e.inv)
      (TwoSquare.mk _ _ _ _
        (rightDerivedFunctorPlusThreeFactorIso L₁ H G L₂ e).inv) K := by
  let : Limits.PreservesFiniteLimits G := G.preservesFiniteLimits_of_preservesHomology
  let : Limits.PreservesFiniteColimits G := G.preservesFiniteColimits_of_preservesHomology
  let : Limits.PreservesFiniteLimits H := H.preservesFiniteLimits_of_preservesHomology
  let : Limits.PreservesFiniteColimits H := H.preservesFiniteColimits_of_preservesHomology
  let : Limits.PreservesFiniteLimits L₁ := L₁.preservesFiniteLimits_of_preservesHomology
  let : Limits.PreservesFiniteColimits L₁ := L₁.preservesFiniteColimits_of_preservesHomology
  let : Limits.PreservesFiniteLimits L₂ := L₂.preservesFiniteLimits_of_preservesHomology
  let : Limits.PreservesFiniteColimits L₂ := L₂.preservesFiniteColimits_of_preservesHomology
  have h := exactComparisonSquareEquation L₁ H G L₂ (G ⋙ L₂) (L₁ ⋙ H)
    (Iso.refl _) (Iso.refl _) e.symm K
  simpa only [rightDerivedFunctorPlusThreeFactorIso,
    rightDerivedFunctorPlusCompIso_eq_of_preservesHomology,
    rightDerivedFunctorPlusIso_refl, rightDerivedFunctorPlusIso_symm,
    Iso.refl_symm, Iso.refl_trans, Iso.trans_refl, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Category.assoc] using h

variable (R₁ : B ⥤ A) (R₂ : D ⥤ C) [R₁.Additive] [R₂.Additive]
  [IsIso (rightDerivedFunctorPlusCompComparison R₁ G)]
  [IsIso (rightDerivedFunctorPlusCompComparison H R₂)]

/-- The full original mate assembly, from the ordinary mate to the specified derived factors. -/
theorem mate_threeFactorInverse_eq_threeFactorDirect
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e : L₁ ⋙ H ≅ G ⋙ L₂) (d : R₁ ⋙ G ≅ H ⋙ R₂)
    (hd : (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ e.inv)).natTrans = d.hom) :
    (mateEquiv adj₁.rightDerivedFunctorPlus adj₂.rightDerivedFunctorPlus
      (TwoSquare.mk _ _ _ _
        (rightDerivedFunctorPlusThreeFactorIso L₁ H G L₂ e).inv)).natTrans =
      (rightDerivedFunctorPlusThreeFactorIso R₁ G H R₂ d).hom := by
  let α := TwoSquare.mk _ _ _ _ e.inv
  apply derivedMate_eq_of_originalUnit adj₁ adj₂ α
    (TwoSquare.mk _ _ _ _ (rightDerivedFunctorPlusThreeFactorIso L₁ H G L₂ e).inv)
    (threeFactorInverse_exactComparison G H L₁ L₂ e)
  intro K
  have hm : ((mateEquiv adj₁ adj₂ α).mapCochainComplexPlus).natTrans.app K =
      (NatIso.mapCochainComplexPlus d).hom.app K := by
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.hom_ext
    intro n
    change (𝟙 _ ≫ (mateEquiv adj₁ adj₂ α).natTrans.app (K.obj.X n) ≫ 𝟙 _) =
      d.hom.app (K.obj.X n)
    simpa only [Category.id_comp, Category.comp_id] using congr_app hd (K.obj.X n)
  change _ = _ ≫ DerivedCategory.Plus.Q.map
    (((mateEquiv adj₁ adj₂ α).mapCochainComplexPlus).natTrans.app K) ≫ _
  rw [hm]
  exact threeFactorComparison_originalUnit G H R₁ R₂ d K

end Inverse

end CategoryTheory
