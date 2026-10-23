/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.Basic.Finite.Sum

/-! # Finite multicospan shapes

The shape of the matching diagram of a finite `1`-hypercover is a finite
category. The two arrows at each relation remain distinct: this category is
not assumed thin.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Limits.WalkingMulticospan

universe w w'

variable (J : MulticospanShape.{w, w'})

/-- The objects of a multicospan with finite left and right indices are finite. -/
instance [Finite J.L] [Finite J.R] : Finite (WalkingMulticospan J) :=
  Finite.of_surjective (Sum.elim left right) (by
    rintro (a | b)
    · exact ⟨Sum.inl a, rfl⟩
    · exact ⟨Sum.inr b, rfl⟩)

/-- The constructor tag distinguishes the arrows between fixed objects. -/
def homTag {a b : WalkingMulticospan J} : (a ⟶ b) → Fin 3
  | .id _ => 0
  | .fst _ => 1
  | .snd _ => 2

/-- Each hom set has at most three elements, without a thinness assumption. -/
theorem homTag_injective (a b : WalkingMulticospan J) :
    Function.Injective (homTag J (a := a) (b := b)) := by
  have hgeneral : ∀ {a b a' b' : WalkingMulticospan J}
      (f : a ⟶ b) (g : a' ⟶ b'), a = a' → b = b' →
        homTag J f = homTag J g → HEq f g := by
    intro a b a' b' f g ha hb h
    cases f <;> cases g <;> simp_all [homTag]
    all_goals cases hb; rfl
  intro f g h
  exact eq_of_heq (hgeneral f g rfl rfl h)

instance (a b : WalkingMulticospan J) : Finite (a ⟶ b) :=
  Finite.of_injective (homTag J) (homTag_injective J a b)

/-- Finite multicospans are finite categories, in their original universes. -/
instance finCategoryOfFiniteLeftAndRight [Finite J.L] [Finite J.R] :
    FinCategory (WalkingMulticospan J) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

end CategoryTheory.Limits.WalkingMulticospan
