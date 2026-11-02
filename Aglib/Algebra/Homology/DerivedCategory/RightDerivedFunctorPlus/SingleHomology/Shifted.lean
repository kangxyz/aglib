/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology

/-! # Original higher homology of a shifted single

The native single shift, derived-functor shift, and homology shift comparisons
identify degree `j + n` of the image of the original degree-`j` single with the
original natural-degree `n` right-derived object. The two derived realizations
remain independent; there is no left-exactness or cohomological-dimension input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v d u' v' d'

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{d} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{d'} B] (F : A ⥤ B) [F.Additive]

/-- The actual shifted single computes the original natural-degree derived
object, through the installed shift and single/homology comparisons. -/
def rightDerivedSingleHomologyShiftedIso (M : A) (j : ℤ) (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor B (j + (n : ℤ))).obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A j).obj M)) ≅
      (F.rightDerived n).obj M := by
  let K := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M)
  let eShift : (DerivedCategory.Plus.homologyFunctor B (j + (n : ℤ))).obj (K⟦-j⟧) ≅
      (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).obj K := by
    change (DerivedCategory.homologyFunctor B (j + (n : ℤ))).obj
        (DerivedCategory.Plus.ι.obj (K⟦-j⟧)) ≅
      (DerivedCategory.homologyFunctor B (n : ℤ)).obj (DerivedCategory.Plus.ι.obj K)
    let e := ((DerivedCategory.homologyFunctor B 0).shiftIso
      (-j) (j + (n : ℤ)) (n : ℤ) (by omega)).app (DerivedCategory.Plus.ι.obj K)
    let e' : (DerivedCategory.homologyFunctor B (j + (n : ℤ))).obj
        ((DerivedCategory.Plus.ι.obj K)⟦-j⟧) ≅
        (DerivedCategory.homologyFunctor B (n : ℤ)).obj (DerivedCategory.Plus.ι.obj K) := by
      simpa only [Functor.comp_obj, DerivedCategory.shift_homologyFunctor] using e
    exact (DerivedCategory.homologyFunctor B (j + (n : ℤ))).mapIso
      ((DerivedCategory.Plus.ι.commShiftIso (-j)).app K) ≪≫ e'
  exact (DerivedCategory.Plus.homologyFunctor B (j + (n : ℤ))).mapIso
      (F.rightDerivedFunctorPlus.mapIso
          (((DerivedCategory.Plus.singleFunctors A).shiftIso (-j) j 0 (by omega)).app M).symm ≪≫
        (F.rightDerivedFunctorPlus.commShiftIso (-j)).app
          ((DerivedCategory.Plus.singleFunctor A 0).obj M)) ≪≫
    eShift ≪≫ ((F.rightDerivedSingleHomologyIso n).app M).symm

end CategoryTheory.Functor
