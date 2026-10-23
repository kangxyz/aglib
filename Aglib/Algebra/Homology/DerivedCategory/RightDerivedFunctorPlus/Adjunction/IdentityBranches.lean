/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Identity
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.ComparisonBranches

/-! # The other two bounded-below composition unit laws -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w u' v' w'
namespace CategoryTheory.Functor
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w'} B] [EnoughInjectives B]
  (F : A ⥤ B) [F.Additive]

omit [EnoughInjectives B] in
/-- The exact-second-factor comparison respects the original left unitor. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesHomology_leftUnitor [F.PreservesHomology] :
    rightDerivedFunctorPlusCompIsoOfPreservesHomology (𝟭 A) F ≪≫
        isoWhiskerRight (rightDerivedFunctorPlusIdIso A) F.rightDerivedFunctorPlus ≪≫
        leftUnitor F.rightDerivedFunctorPlus =
      (𝟭 A ⋙ F).rightDerivedFunctorPlusIso (leftUnitor F) := by
  rw [rightDerivedFunctorPlusCompIsoOfPreservesHomology_eq_ofPreservesInjectives]
  exact rightDerivedFunctorPlusCompIsoOfPreservesInjectives_leftUnitor F

/-- The injective-preserving-first-factor comparison respects the original right unitor. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesInjectives_rightUnitor
    [F.PreservesInjectiveObjects] :
    rightDerivedFunctorPlusCompIsoOfPreservesInjectives F (𝟭 B) ≪≫
        isoWhiskerLeft F.rightDerivedFunctorPlus (rightDerivedFunctorPlusIdIso B) ≪≫
        rightUnitor F.rightDerivedFunctorPlus =
      (F ⋙ 𝟭 B).rightDerivedFunctorPlusIso (rightUnitor F) := by
  rw [← rightDerivedFunctorPlusCompIsoOfPreservesHomology_eq_ofPreservesInjectives]
  exact rightDerivedFunctorPlusCompIsoOfPreservesHomology_rightUnitor F

end CategoryTheory.Functor
