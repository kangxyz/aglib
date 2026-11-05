/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Additive transport of the original identity annihilator -/

@[expose] public section
namespace CategoryTheory.Functor

/-- An additive functor preserves the original natural-number annihilator. -/
theorem map_nsmul_id_eq_zero
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (A : C) (n : ℕ) (h : n • 𝟙 A = 0) :
    n • 𝟙 (F.obj A) = 0 := by
  have hz := congrArg F.map h
  rw [F.map_nsmul, F.map_id, F.map_zero] at hz
  exact hz

end CategoryTheory.Functor
