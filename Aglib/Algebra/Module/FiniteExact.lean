/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite generation of the middle term of an exact pair

Surjectivity onto the final module is unnecessary when that module is
Noetherian: corestrict the second map to its actual range and use the native
finite-module exact-sequence theorem.
-/

@[expose] public section

namespace Module.Finite

variable {R M N P : Type*} [Ring R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

/-- An exact pair with finite source and Noetherian final module has finite
middle module; the second map need not be surjective. -/
theorem of_exact_of_noetherian {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) [Module.Finite R M] [IsNoetherian R P] :
    Module.Finite R N := by
  have he : Function.Exact f g.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
    exact LinearMap.exact_iff.mp h
  exact Module.Finite.of_exact he g.surjective_rangeRestrict

end Module.Finite
