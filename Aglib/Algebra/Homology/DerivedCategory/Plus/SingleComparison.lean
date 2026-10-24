/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Shift.CommShift

/-! # Transport of original comparisons between single degrees

A shift-compatible natural transformation is invertible on every single of
an object when it is invertible on that object's degree-zero single. The proof
is carried out at the abstract transformation, before geometric specialization.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace DerivedCategory.Plus

universe u v d u' v'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{d} C]
  {D : Type u'} [Category.{v'} D] [HasShift D ℤ]
  {F G : Plus C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
  (τ : F ⟶ G) [τ.CommShift ℤ]

/-- Native shift compatibility propagates the original degree-zero single comparison. -/
theorem isIso_app_single_of_zero (M : C) (i : ℤ)
    [IsIso (τ.app ((singleFunctor C 0).obj M))] :
    IsIso (τ.app ((singleFunctor C i).obj M)) := by
  let K := (singleFunctor C 0).obj M
  have hs : IsIso (τ.app (K⟦-i⟧)) := by
    rw [τ.app_shift (-i) K]
    infer_instance
  let e : K⟦-i⟧ ≅ (singleFunctor C i).obj M :=
    ((singleFunctors C).shiftIso (-i) i 0 (by omega)).app M
  exact (NatTrans.isIso_app_iff_of_iso τ e).mp hs

end DerivedCategory.Plus
