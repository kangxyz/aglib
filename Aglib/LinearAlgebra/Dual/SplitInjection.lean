/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Algebra.Module.Projective

/-!
# Splitting injections by dual surjectivity

Surjectivity of the dual map splits a map out of a reflexive module whose dual
is projective. The construction uses the native evaluation equivalence and a
projective lift; no duality equivalence for the target is required.
-/

@[expose] public section

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

/-- A map out of a reflexive module with projective dual splits when its dual
map is surjective. -/
theorem exists_leftInverse_of_surjective_dualMap [Module.IsReflexive R M]
    [Module.Projective R (Module.Dual R M)] (f : M →ₗ[R] N)
    (hf : Function.Surjective f.dualMap) :
    ∃ g : N →ₗ[R] M, g.comp f = LinearMap.id := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.dualMap LinearMap.id hf
  let g := (Module.evalEquiv R M).symm.toLinearMap.comp
    (s.dualMap.comp (Module.Dual.eval R N))
  refine ⟨g, ?_⟩
  ext m
  apply (Module.evalEquiv R M).injective
  ext φ
  simpa [g] using LinearMap.congr_fun (LinearMap.congr_fun hs φ) m

end LinearMap
