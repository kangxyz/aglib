/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ZeroComparison

/-! # UnitIsIso -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory.Functor
universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃ u₄ v₄ w₄

section SingleUnit
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B] (F : A ⥤ B) [F.Additive]

/-- Invertibility of the original unit at the single complex suffices for
invertibility of the same normalized single unit. -/
theorem isIso_rightDerivedSingleUnit_of_isIso_unit (M : A)
    [IsIso (F.rightDerivedFunctorPlusUnit.app
      ((CochainComplex.singleFunctorPlus A 0).obj M))] :
    IsIso (F.rightDerivedSingleUnit M) := by
  let e : (CochainComplex.singleFunctorPlus B 0).obj (F.obj M) ≅
      F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus A 0).obj M) :=
    ObjectProperty.isoMk _ ((singleMapHomologicalComplex F (.up ℤ) 0).app M).symm
  change IsIso (DerivedCategory.Plus.Q.map e.hom ≫
    F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus A 0).obj M))
  infer_instance

end SingleUnit

end CategoryTheory.Functor
