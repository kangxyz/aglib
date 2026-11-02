/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-! # All natural-degree homology detects invertibility on nonnegative objects

The same native bounded-below derived category is used throughout. Homology in
negative degrees vanishes on the two given nonnegative objects, so the native
all-integer criterion reduces exactly to every natural degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory.Plus

universe u v d

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{d} C]

/-- A morphism between nonnegative native D+ objects is invertible exactly
when its homology maps in all natural degrees are invertible. -/
theorem isIso_iff_homology_nat {X Y : Plus C} [X.IsGE 0] [Y.IsGE 0]
    (f : X ⟶ Y) : IsIso f ↔ ∀ q : ℕ, IsIso ((homologyFunctor C (q : ℤ)).map f) := by
  constructor
  · intro hf q
    have := hf
    infer_instance
  · intro hf
    apply (isIso_iff f).mpr
    intro k
    by_cases hk : k < 0
    · exact (isZero_homology_of_isGE X 0 k hk).isIso
        (isZero_homology_of_isGE Y 0 k hk) _
    · have he : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (le_of_not_gt hk)
      rw [← he]
      exact hf k.toNat

end DerivedCategory.Plus
