/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.SourceCoherence
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Comparison.ThreeFactor
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.PullbackCoherence
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SingleSquare

/-!
# Original exact source squares through the installed three-factor comparison

The original factored comparison, its exact-complex law and its single-object
law are retained. Each abelian category uses its already selected realization.
-/

@[expose] public noncomputable section

namespace CategoryTheory

open CategoryTheory.Functor

universe uA vA wA uB vB wB uC vC wC uD vD wD

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : A ⥤ B) (H : B ⥤ D) (G : A ⥤ C) (V : C ⥤ D)
  [F.Additive] [H.Additive] [G.Additive] [V.Additive]
  [F.PreservesHomology] [H.PreservesHomology]
  [G.PreservesHomology] [V.PreservesHomology]

local instance sourceComparisonIsIso :
    IsIso (rightDerivedFunctorPlusCompComparison G V) :=
  isIso_rightDerivedFunctorPlusCompComparison_of_preservesHomology G V

local instance targetComparisonIsIso :
    IsIso (rightDerivedFunctorPlusCompComparison F H) :=
  isIso_rightDerivedFunctorPlusCompComparison_of_preservesHomology F H

omit [F.PreservesHomology] [G.PreservesHomology] in
/-- The installed three-factor comparison is exactly the original factored square. -/
theorem rightDerivedFunctorPlusThreeFactorIso_eq_factored
    (M N : A ⥤ D) [M.Additive] [N.Additive]
    (eA : M ≅ G ⋙ V) (eB : N ≅ F ⋙ H) (t : M ≅ N) :
    rightDerivedFunctorPlusThreeFactorIso G V F H (sourceSquareIso eA eB t) =
      sourceSquareIso
        (M.rightDerivedFunctorPlusIso eA ≪≫
          rightDerivedFunctorPlusCompIsoOfPreservesHomology G V)
        (N.rightDerivedFunctorPlusIso eB ≪≫
          rightDerivedFunctorPlusCompIsoOfPreservesHomology F H)
        (M.rightDerivedFunctorPlusIso t) := by
  simp only [rightDerivedFunctorPlusThreeFactorIso, sourceSquareIso,
    rightDerivedFunctorPlusCompIso_eq_of_preservesHomology,
    rightDerivedFunctorPlusIso_trans, rightDerivedFunctorPlusIso_symm,
    Iso.trans_symm, Iso.trans_assoc]

/-- The exact-complex comparison uses the actual ordinary square. -/
theorem rightDerivedFunctorPlusThreeFactorIso_exactComparison
    (e : G ⋙ V ≅ F ⋙ H) (K : CochainComplex.Plus A) :
    ExactComparisonSquareEquation F H G V
      (TwoSquare.mk _ _ _ _ e.hom)
      (TwoSquare.mk _ _ _ _ (rightDerivedFunctorPlusThreeFactorIso G V F H e).hom) K := by
  let : Limits.PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  let : Limits.PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesHomology
  let : Limits.PreservesFiniteLimits H := H.preservesFiniteLimits_of_preservesHomology
  let : Limits.PreservesFiniteColimits H := H.preservesFiniteColimits_of_preservesHomology
  let : Limits.PreservesFiniteLimits G := G.preservesFiniteLimits_of_preservesHomology
  let : Limits.PreservesFiniteColimits G := G.preservesFiniteColimits_of_preservesHomology
  let : Limits.PreservesFiniteLimits V := V.preservesFiniteLimits_of_preservesHomology
  let : Limits.PreservesFiniteColimits V := V.preservesFiniteColimits_of_preservesHomology
  have h := exactComparisonSquareEquation F H G V (G ⋙ V) (F ⋙ H)
    (Iso.refl _) (Iso.refl _) e K
  simpa only [rightDerivedFunctorPlusThreeFactorIso,
    rightDerivedFunctorPlusCompIso_eq_of_preservesHomology,
    rightDerivedFunctorPlusIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl] using h

/-- The same exact square retains its original single-object comparison. -/
theorem rightDerivedFunctorPlusThreeFactorIso_single
    (e : G ⋙ V ≅ F ⋙ H) (T : A) :
    SingleComparisonSquareEquation F H G V e.hom
      (rightDerivedFunctorPlusThreeFactorIso G V F H e).hom T :=
  singleComparisonSquareEquation F H G V _ _ T
    (rightDerivedFunctorPlusThreeFactorIso_exactComparison F H G V e
      ((CochainComplex.singleFunctorPlus A 0).obj T))

end CategoryTheory
