/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Logic.Function.Basic

/-! # Injectivity and surjectivity in an actual commuting square

The four carriers have independent universes. The square retains its supplied
functions; the transport needs only the indicated one-sided properties of the
vertical functions.
-/

@[expose] public section

namespace Function

universe uA uB uA' uB'

variable {A : Sort uA} {B : Sort uB} {A' : Sort uA'} {B' : Sort uB'}
  {f : A → B} {f' : A' → B'} {i : A → A'} {j : B → B'}

/-- Surjectivity transports through the supplied commuting square when its
right edge is surjective. -/
theorem surjective_of_commutative_square (h : f' ∘ i = j ∘ f)
    (hj : Surjective j) (hf : Surjective f) : Surjective f' := by
  have hcomp : Surjective (f' ∘ i) := h.symm ▸ hj.comp hf
  exact hcomp.of_comp

/-- Injectivity transports through the supplied square when the right edge is
injective and the left edge is surjective. -/
theorem injective_of_commutative_square (h : f' ∘ i = j ∘ f)
    (hj : Injective j) (hi : Surjective i) (hf : Injective f) : Injective f' := by
  have hcomp : Injective (f' ∘ i) := h.symm ▸ hj.comp hf
  exact hcomp.of_comp_right hi

end Function
