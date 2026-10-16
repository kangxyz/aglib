/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Exact.Sequence
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite generation at the middle of an exact sequence

An exact pair of linear maps has a finitely generated middle module if the
source is finitely generated and the target is Noetherian. The second map
need not be surjective: its actual image is a finite submodule of the target.
The coefficient ring and all three module universes are independent.
-/

@[expose] public section

namespace Module.Finite

variable {R A B C : Type*} [Ring R]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]

/-- Finite source and Noetherian target give a finite middle module for an exact pair. -/
theorem of_exact_of_isNoetherian (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (h : Function.Exact f g) [Module.Finite R A] [IsNoetherian R C] :
    Module.Finite R B :=
  Module.Finite.of_exact h.linearMap_rangeRestrict g.surjective_rangeRestrict

end Module.Finite
