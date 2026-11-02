/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.CoefficientBound

/-!
# Natural same-degree exact coefficient comparison

An actual bounded-below derived comparison induces the same-degree comparison
of the original higher derived functors. The natural isomorphism retains every
original coefficient map; it does not
require coefficient forgetting to preserve injectives.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃ u₄ v₄ w₄

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  [EnoughInjectives B]
  {A' : Type u₃} [Category.{v₃} A'] [Abelian A'] [HasDerivedCategory.{w₃} A']
  [EnoughInjectives A']
  {B' : Type u₄} [Category.{v₄} B'] [Abelian B'] [HasDerivedCategory.{w₄} B']
  (F : A ⥤ B) (F' : A' ⥤ B') (U : A ⥤ A') (V : B ⥤ B')
  [F.Additive] [F'.Additive] [U.Additive] [V.Additive]
  [U.PreservesHomology] [V.PreservesHomology]
  (e : F.rightDerivedFunctorPlus ⋙ V.rightDerivedFunctorPlus ≅
    U.rightDerivedFunctorPlus ⋙ F'.rightDerivedFunctorPlus)

/-- Natural comparison of original higher derived functors through the same
exact coefficient square. This upgrades the existing objectwise construction
without making an unrelated choice of isomorphisms. -/
def rightDerivedExactCoefficientIso (n : ℕ) :
    F.rightDerived n ⋙ V ≅ U ⋙ F'.rightDerived n :=
  isoWhiskerRight (F.rightDerivedSingleHomologyIso n) V ≪≫
    isoWhiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
      (isoWhiskerLeft F.rightDerivedFunctorPlus
        (V.rightDerivedFunctorPlusHomologyIso (n : ℤ)).symm) ≪≫
    isoWhiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
      (isoWhiskerRight e (DerivedCategory.Plus.homologyFunctor B' (n : ℤ))) ≪≫
    isoWhiskerRight (U.rightDerivedFunctorPlusSingleIso 0)
      (F'.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B' (n : ℤ)) ≪≫
    isoWhiskerLeft U (F'.rightDerivedSingleHomologyIso n).symm

/-- Each component is the pre-existing original same-degree comparison. -/
theorem rightDerivedExactCoefficientIso_app (n : ℕ) (M : A) :
    (rightDerivedExactCoefficientIso F F' U V e n).app M =
      rightDerivedObjExactCoefficientIso F F' U V e M n := rfl

end CategoryTheory.Functor
