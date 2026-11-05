/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-! # Original higher-image bounds on the native derived single

A natural-degree vanishing bound is an upper cohomological bound on the same
bounded-below derived single. No unbounded resolution or replacement model
is needed for this comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits

universe u v u' v' w w'

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory.{w} A]
    {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
    (F : A ⥤ B) [F.Additive]

/-- Natural-degree vanishing above N gives the corresponding upper bound on
an original degree-zero single under the installed bounded-below derivative. -/
theorem rightDerivedFunctorPlus_single_isLE_of_bound (M : A) (N : ℕ)
    (h : ∀ q : ℕ, N < q → IsZero ((F.rightDerived q).obj M)) :
    (F.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor A 0).obj M)).IsLE (N : ℤ) := by
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  intro q hq
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ q by omega)
  exact (h n (by omega)).of_iso ((F.rightDerivedSingleHomologyIso n).app M).symm

end CategoryTheory.Functor
