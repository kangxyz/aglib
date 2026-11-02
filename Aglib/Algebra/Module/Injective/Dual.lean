/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.LeftExact

/-!
# Exact native dual maps over a self-injective commutative ring

If a commutative ring is injective over itself, precomposition with an injective
linear map is surjective on native module duals, and dualization reverses every
exact pair of linear maps. In particular it reverses short exact sequences.
All module universes are independent; no finiteness or field hypothesis is used.
The maps are Mathlib's `LinearMap.dualMap`, with its existing identity,
composition and evaluation-naturality laws. No replacement dual is introduced.

Sources: Mathlib `Algebra/Module/Injective.lean`, the extension property;
`LinearAlgebra/LeftExact.lean`, exactness of the original Hom precomposition maps.
-/

@[expose] public noncomputable section

namespace Module.Injective

variable {R : Type*} [CommRing R] [Module.Injective R R]
  {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

/-- Native dual precomposition along an injective map is surjective over a self-injective ring. -/
theorem dualMap_surjective (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Surjective f.dualMap := by
  intro g
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R R M N f hf g
  exact ⟨h, hh⟩

/-- Dualization reverses every exact pair through its original precomposition maps. -/
theorem dualMap_exact (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hfg : Function.Exact f g) :
    Function.Exact g.dualMap f.dualMap := by
  have hfg' : Function.Exact f g.rangeRestrict :=
    g.range.injective_subtype.comp_exact_iff_exact.mp hfg
  have hx := LinearMap.exact_lcomp_of_exact_of_surjective R hfg' g.surjective_rangeRestrict
  intro a
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := (hx a).mp ha
    obtain ⟨c, hc⟩ := Module.Injective.extension_property R R g.range P
      g.range.subtype g.range.injective_subtype b
    refine ⟨c, ?_⟩
    ext x
    exact (DFunLike.congr_fun hc (g.rangeRestrict x)).trans (DFunLike.congr_fun hb x)
  · rintro ⟨a, rfl⟩
    ext x
    change a (g (f x)) = 0
    rw [hfg.apply_apply_eq_zero, map_zero]

/-- A short exact sequence reverses to a short exact sequence of the actual module duals. -/
theorem dualMap_shortExact (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Injective g.dualMap ∧ Function.Exact g.dualMap f.dualMap ∧
      Function.Surjective f.dualMap :=
  ⟨LinearMap.dualMap_injective_of_surjective hg, dualMap_exact f g hfg,
    dualMap_surjective f hf⟩

end Module.Injective
