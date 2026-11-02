/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction
public import Aglib.CategoryTheory.Adjunction.Mates.Whole

/-!
# The original right-derived unit as a canonical mate

The localization square for an exact left adjoint has the original right-derived
unit as its mate. This is the compatibility needed before comparing ordinary and
derived exchange maps. No invertibility of the right-derived unit is asserted.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v u' v' w w'

namespace CategoryTheory.Adjunction

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w'} B] [EnoughInjectives B]
  {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive] [L.PreservesHomology]

/-- The mate of the exact localization comparison is the actual right-derived unit. -/
theorem rightDerivedFunctorPlusUnit_eq_mate (adj : L ⊣ R) :
    R.rightDerivedFunctorPlusUnit =
      (mateEquiv adj.mapCochainComplexPlus adj.rightDerivedFunctorPlus
        (TwoSquare.mk _ _ _ _ L.rightDerivedFunctorPlusExactComparison.hom)).natTrans := by
  apply (eq_mateEquiv_iff adj.mapCochainComplexPlus adj.rightDerivedFunctorPlus
    (TwoSquare.mk _ _ _ _ L.rightDerivedFunctorPlusExactComparison.hom)
    R.rightDerivedFunctorPlusUnit).2
  intro K
  exact adj.rightDerivedFunctorPlus_counit_fac K

end CategoryTheory.Adjunction
