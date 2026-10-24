/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Logic.Function.Basic

/-! # Pairing actual cycle witnesses before specialization

Keep the original class, term and projection functions opaque while choosing
representatives and pairing cycles. The witness predicate is the literal pair
of term and projection equations, not an additional cohomological assumption.
-/

@[expose] public section

namespace CategoryTheory.Functor

/-- An actual cycle with its specified term and specified projected class. -/
def CycleWitness {Z : Type*} {A : Type*} {P : Type*}
    (i : Z → A) (π : Z → P) (a : A) (x : P) : Prop :=
  ∃ z, i z = a ∧ x = π z

/-- Convert a producer's reversed pair of equations before substituting its
actual class, cycle and term types. -/
theorem cycleWitness_of_reversed {Z : Type*} {A : Type*} {P : Type*}
    (i : Z → A) (π : Z → P) (a : A) (x : P)
    (h : ∃ z, x = π z ∧ i z = a) : CycleWitness i π a x := by
  obtain ⟨z, hp, hi⟩ := h
  exact ⟨z, hi, hp⟩

/-- Pair actual source and target cycle producers and descend from a surjective
representative constructor. All substitution and term congruence occur while
these maps and their carriers are parameters. -/
theorem pairedCycles_of_representatives {H : Type*} {R : Type*}
    {Z : Type*} {Z' : Type*} {A : Type*} {B : Type*} {P : Type*} {P' : Type*}
    (Q : R → Prop) (mk : ∀ r, Q r → H)
    (hmk : ∀ x, ∃ r hr, mk r hr = x)
    (i : Z → A) (π : Z → P) (v : H → P)
    (j : Z' → B) (π' : Z' → P') (v' : H → P')
    (a : R → A) (l : A → B)
    (hs : ∀ r hr, CycleWitness i π (a r) (v (mk r hr)))
    (ht : ∀ r hr, CycleWitness j π' (l (a r)) (v' (mk r hr))) (x : H) :
    ∃ z z', v x = π z ∧ v' x = π' z' ∧ j z' = l (i z) := by
  obtain ⟨r, hr, rfl⟩ := hmk x
  obtain ⟨z, hi, hp⟩ := hs r hr
  obtain ⟨z', hj, hp'⟩ := ht r hr
  exact ⟨z, z', hp, hp', hj.trans (congrArg l hi.symm)⟩

end CategoryTheory.Functor
