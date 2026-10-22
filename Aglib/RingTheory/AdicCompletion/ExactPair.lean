/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdicCompletion.Exactness

/-!
# Completion of an exact pair of finite modules

Factor through the actual images to apply native short-exact completion.
The first map need not be injective and the second need not be surjective.
The module universe matches the native Noetherian exactness supplier.
-/

@[expose] public section

namespace AdicCompletion

universe u
variable {R M N P : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P] [Module.Finite R N] [Module.Finite R P]

/-- Completion preserves an exact pair with finite middle and target modules.
No injectivity or surjectivity is silently added to the original maps. -/
theorem map_exact_pair (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hfg : Function.Exact f g) : Function.Exact (map I f) (map I g) := by
  have hex : Function.Exact (map I f.range.subtype) (map I g.rangeRestrict) :=
    map_exact (I := I) Subtype.val_injective hfg.linearMap_rangeRestrict
      g.surjective_rangeRestrict
  have hinj : Function.Injective (map I g.range.subtype) :=
    map_injective I Subtype.val_injective
  have hsurj : Function.Surjective (map I f.rangeRestrict) :=
    map_surjective I f.surjective_rangeRestrict
  intro y
  constructor
  · intro hy
    have hy' : map I g.rangeRestrict y = 0 := by
      apply hinj
      rw [_root_.map_zero, map_comp_apply, LinearMap.subtype_comp_rangeRestrict]
      exact hy
    obtain ⟨z, hz⟩ := (hex y).mp hy'
    obtain ⟨x, rfl⟩ := hsurj z
    refine ⟨x, ?_⟩
    simpa only [map_comp_apply, LinearMap.subtype_comp_rangeRestrict] using hz
  · rintro ⟨x, rfl⟩
    rw [map_comp_apply, hfg.linearMap_comp_eq_zero, AdicCompletion.map_zero]
    rfl

end AdicCompletion
