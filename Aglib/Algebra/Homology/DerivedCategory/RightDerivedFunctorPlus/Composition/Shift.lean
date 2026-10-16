/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition
public import Aglib.Algebra.Homology.CochainComplexPlus.Shift

/-!
# Shifts of the original right-derived composition unit

The installed composition unit is a composition of the original termwise
comparison, the two original derived units and native associators. Each
factor commutes with the supplied native integer shifts. No exactness or
invertibility hypothesis on a derived comparison is required.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe uA vA wA uB vB wB uC vC wC

namespace CategoryTheory.Functor

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    [EnoughInjectives A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    [EnoughInjectives B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]

/-- The original derived composition unit commutes with native shifts,
without an exactness or injective-preservation hypothesis on F or G. -/
instance rightDerivedFunctorPlusCompUnit_commShift :
    (rightDerivedFunctorPlusCompUnit F G).CommShift ℤ := by
  dsimp only [rightDerivedFunctorPlusCompUnit]
  infer_instance

end CategoryTheory.Functor
