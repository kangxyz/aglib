/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Preadditive.Basic

/-! # Returning the represented trace through the original image adjunction

The left-adjoint comparison is constructed by adjunction uniqueness. Its unit
normalization proves the rank relation for the original inverse image.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Adjunction

universe u v u' v'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R)

/-- Transport the given trace by the canonical comparison of the actual adjoints. -/
def traceThroughLeftAdjointUniq (τ : L' ⋙ R ⟶ 𝟭 C) : L ⋙ R ⟶ 𝟭 C :=
  Functor.whiskerRight (adj.leftAdjointUniq adj').hom R ≫ τ

/-- The original unit retains the given rank after canonical adjoint transport. -/
theorem traceThroughLeftAdjointUniq_rank [Preadditive C]
    (τ : L' ⋙ R ⟶ 𝟭 C) (n : ℕ) (F : C)
    (hτ : adj'.unit.app F ≫ τ.app F = n • 𝟙 F) :
    adj.unit.app F ≫ (traceThroughLeftAdjointUniq adj adj' τ).app F = n • 𝟙 F := by
  change adj.unit.app F ≫ (R.map ((adj.leftAdjointUniq adj').hom.app F) ≫ τ.app F) = _
  rw [← Category.assoc, unit_leftAdjointUniq_hom_app]
  exact hτ

end CategoryTheory.Adjunction
