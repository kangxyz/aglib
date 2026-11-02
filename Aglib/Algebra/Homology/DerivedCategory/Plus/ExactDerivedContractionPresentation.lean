/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExactDerivedContractionModels
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.PullbackCoherence
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.ComparisonBranches
/-! # An original composite presentation of a derived contraction -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace DerivedCategory.Plus
universe u v d u' v' d'
variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{d} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [EnoughInjectives B]
  [HasDerivedCategory.{d'} B]
  (F : A ⥤ B) (G : B ⥤ A) (P : A ⥤ A) [F.Additive] [G.Additive] [P.Additive]
  [F.PreservesInjectiveObjects] [G.PreservesHomology]

/-- The native injective-composition presentation retains the exact original contraction. -/
theorem exactDerivedContractionViaIso_presentation (c : P ≅ F ⋙ G) (e : P ≅ 𝟭 A) :
    (P.rightDerivedFunctorPlusIso c ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G).symm ≪≫
      P.rightDerivedFunctorPlusIso e ≪≫ rightDerivedFunctorPlusIdIso A =
    exactDerivedContractionViaIso F G (c.symm ≪≫ e) := by
  simp only [exactDerivedContractionViaIso, Iso.trans_symm, Iso.trans_assoc,
    rightDerivedFunctorPlusIso_trans, rightDerivedFunctorPlusIso_symm,
    rightDerivedFunctorPlusCompIsoOfPreservesHomology_eq_ofPreservesInjectives]
end DerivedCategory.Plus
