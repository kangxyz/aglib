/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology

/-!
# Same-degree cohomological bounds through exact coefficient comparison

An actual bounded-below derived comparison induces the same-degree comparison
of the original higher derived functors. Faithful exact forgetting reflects
vanishing. It need not preserve injective objects.
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

/-- The original higher derived objects compare through the actual derived
coefficient square, native single and exact homology comparisons. -/
def rightDerivedObjExactCoefficientIso (M : A) (n : ℕ) :
    V.obj ((F.rightDerived n).obj M) ≅ (F'.rightDerived n).obj (U.obj M) :=
  V.mapIso ((F.rightDerivedSingleHomologyIso n).app M) ≪≫
    ((V.rightDerivedFunctorPlusHomologyIso (n : ℤ)).app
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M))).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor B' (n : ℤ)).mapIso
      (e.app ((DerivedCategory.Plus.singleFunctor A 0).obj M)) ≪≫
    (DerivedCategory.Plus.homologyFunctor B' (n : ℤ)).mapIso
      (F'.rightDerivedFunctorPlus.mapIso ((U.rightDerivedFunctorPlusSingleIso 0).app M)) ≪≫
    ((F'.rightDerivedSingleHomologyIso n).app (U.obj M)).symm

include e

/-- Faithful exact coefficient forgetting reflects same-degree original
higher-derived vanishing, with no injectivity-preservation hypothesis. -/
theorem isZero_rightDerived_obj_of_exactCoefficient [V.Faithful]
    (M : A) (n : ℕ) (h : IsZero ((F'.rightDerived n).obj (U.obj M))) :
    IsZero ((F.rightDerived n).obj M) := by
  have hz : IsZero (V.obj ((F.rightDerived n).obj M)) :=
    (rightDerivedObjExactCoefficientIso F F' U V e M n).isZero_iff.mpr h
  apply (IsZero.iff_id_eq_zero _).mpr
  apply V.map_injective
  rw [V.map_id, V.map_zero]
  exact hz.eq_of_src _ _

end CategoryTheory.Functor
