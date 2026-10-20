/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Integer-linear maps on additive notation for units

This is the canonical `Units.map`, converted to additive notation and bundled
as an integer-linear map. It replaces the K-specific compatibility export in
`lean/R5Lab/Aglib/RingTheory/Units/LinearMap.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690` for generic consumers.
-/

@[expose] public section

namespace Units

universe u v

/-- The map on units of a commutative monoid, in integer-linear additive notation. -/
def mapAdditiveLinear {M : Type u} {N : Type v} [CommMonoid M] [CommMonoid N] (f : M →* N) :
    Additive Mˣ →ₗ[ℤ] Additive Nˣ :=
  (Units.map f).toAdditive.toIntLinearMap

@[simp] theorem mapAdditiveLinear_apply {M : Type u} {N : Type v} [CommMonoid M] [CommMonoid N]
    (f : M →* N) (x : Mˣ) :
    mapAdditiveLinear f (Additive.ofMul x) = Additive.ofMul (Units.map f x) := rfl

end Units
