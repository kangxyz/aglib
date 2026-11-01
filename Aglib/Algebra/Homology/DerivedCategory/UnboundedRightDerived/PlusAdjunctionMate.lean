/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.PlusAdjunction
public import Aglib.CategoryTheory.Adjunction.UnderlyingMate

/-! # The actual adjunction mate of bounded-below inclusion -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe s u v w u' v' w'

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  [IsGrothendieckAbelian.{s} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (adj : L ⊣ R)

/-- The mate of the fixed exact-left inclusion square is the same fixed
right-derived comparison, by the original unit equation. -/
theorem unboundedRightDerivedAdjunction_plus_mate :
    (mateEquiv adj.rightDerivedFunctorPlus adj.unboundedRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ L.rightDerivedFunctorPlusCompιIso.inv)).natTrans =
      R.unboundedRightDerivedFunctorPlusIso.hom :=
  mateEquiv_inv_natTrans_eq_of_unit
    adj.rightDerivedFunctorPlus adj.unboundedRightDerivedAdjunction
    L.rightDerivedFunctorPlusCompιIso R.unboundedRightDerivedFunctorPlusIso.hom
    adj.unboundedRightDerivedAdjunction_plus_unit

end CategoryTheory.Adjunction
