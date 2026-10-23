/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-!
# Absolute postcomposition of the installed bounded-below derived functor

The injective-model criterion proves right-derivedness after arbitrary
postcomposition. For an exact functor the inverse of the original unit also
gives left-derivedness, including after arbitrary postcomposition.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v u' v' w w' u'' v''

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w'} B] (F : A ⥤ B) [F.Additive]
  {E : Type u''} [Category.{v''} E]

/-- Arbitrary postcomposition preserves the right-derived universal property of the
original unit, because that unit is invertible on the native injective models. -/
theorem isRightDerivedFunctor_rightDerivedFunctorPlus_postcomp
    (H : DerivedCategory.Plus B ⥤ E) :
    (F.rightDerivedFunctorPlus ⋙ H).IsRightDerivedFunctor
      (whiskerRight F.rightDerivedFunctorPlusUnit H ≫ (associator _ _ _).hom)
      (CochainComplex.Plus.quasiIso A) := by
  have h : (CochainComplex.Plus.localizerMorphism A).Derives
      ((F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) ⋙ H) := by
    intro K J f hf
    have : IsIso ((F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).map
        ((CochainComplex.Plus.localizerMorphism A).functor.map f)) :=
      CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus F f hf
    change IsIso (H.map ((F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).map
      ((CochainComplex.Plus.localizerMorphism A).functor.map f)))
    infer_instance
  apply h.isRightDerivedFunctor_of_isIso
  intro K
  dsimp
  infer_instance

variable [F.PreservesHomology]

/-- The exact comparison is the inverse of the installed original derived unit. -/
def rightDerivedFunctorPlusExactComparison :
    DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus ≅
      F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q := by
  letI : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  exact (asIso F.rightDerivedFunctorPlusUnit).symm

/-- Exact descent is also the left-derived functor, through the same original unit. -/
theorem isLeftDerivedFunctor_rightDerivedFunctorPlus :
    F.rightDerivedFunctorPlus.IsLeftDerivedFunctor
      F.rightDerivedFunctorPlusExactComparison.hom (CochainComplex.Plus.quasiIso A) :=
  isLeftDerivedFunctor_of_inverts (CochainComplex.Plus.quasiIso A) _
    F.rightDerivedFunctorPlusExactComparison

/-- Postcomposition of the exact comparison retains its left-derived universal property. -/
theorem isLeftDerivedFunctor_rightDerivedFunctorPlus_postcomp
    (H : DerivedCategory.Plus B ⥤ E) :
    (F.rightDerivedFunctorPlus ⋙ H).IsLeftDerivedFunctor
      ((associator _ _ _).inv ≫ whiskerRight F.rightDerivedFunctorPlusExactComparison.hom H)
      (CochainComplex.Plus.quasiIso A) :=
  isLeftDerivedFunctor_of_inverts (CochainComplex.Plus.quasiIso A) _
    ((associator _ _ _).symm ≪≫ isoWhiskerRight F.rightDerivedFunctorPlusExactComparison H)

end CategoryTheory.Functor
