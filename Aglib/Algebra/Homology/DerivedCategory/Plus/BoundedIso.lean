/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-! # Intrinsic boundedness of original isomorphic bounded-below objects -/

@[expose] public noncomputable section
open CategoryTheory
namespace DerivedCategory.Plus
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The two original t-structure bounds transport without choosing representatives. -/
theorem exists_bounds_iff_of_iso {K L : Plus A} (e : K ≅ L) :
    (∃ a b : ℤ, K.IsGE a ∧ K.IsLE b) ↔ (∃ a b : ℤ, L.IsGE a ∧ L.IsLE b) := by
  suffices h : ∀ {K L : Plus A}, (K ≅ L) →
      (∃ a b : ℤ, K.IsGE a ∧ K.IsLE b) → ∃ a b : ℤ, L.IsGE a ∧ L.IsLE b from
    ⟨h e, h e.symm⟩
  intro K L e ⟨a, b, ha, hb⟩
  let : K.IsGE a := ha
  let : K.IsLE b := hb
  exact ⟨a, b, TStructure.t.isGE_of_iso e a, TStructure.t.isLE_of_iso e b⟩

end DerivedCategory.Plus
