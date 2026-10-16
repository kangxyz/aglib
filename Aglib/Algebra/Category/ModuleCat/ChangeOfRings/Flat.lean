/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Exact scalar extension along a flat ring map

The native scalar-extension functor preserves exact sequences along a flat
ring map, hence finite limits and finite colimits. Ring and module carrier
universes are independent. The flatness premise is the native `RingHom.Flat`
property of the specified map; no ambient algebra structure is chosen by the
interface.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

universe u v w

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S]

/-- Flat scalar extension preserves an actual module short-complex exactness statement. -/
theorem extendScalars_map_exact_of_flat (φ : R →+* S) (hφ : φ.Flat)
    (C : ShortComplex (ModuleCat.{v} R)) (hC : C.Exact) :
    (C.map (extendScalars φ)).Exact := by
  let := φ.toAlgebra
  let : Module.Flat R S := hφ
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hC ⊢
  exact Module.Flat.lTensor_exact S hC

/-- The native scalar-extension functor along a flat map preserves finite limits. -/
theorem extendScalars_preservesFiniteLimits_of_flat (φ : R →+* S) (hφ : φ.Flat) :
    PreservesFiniteLimits (extendScalars.{u, w, v} φ) := by
  have h := ((Functor.exact_tfae (extendScalars.{u, w, v} φ)).out 2 4).mp
    (extendScalars_map_exact_of_flat φ hφ)
  exact h.1

/-- The native scalar-extension functor along a flat map preserves finite colimits. -/
theorem extendScalars_preservesFiniteColimits_of_flat (φ : R →+* S) (hφ : φ.Flat) :
    PreservesFiniteColimits (extendScalars.{u, w, v} φ) := by
  have h := ((Functor.exact_tfae (extendScalars.{u, w, v} φ)).out 2 4).mp
    (extendScalars_map_exact_of_flat φ hφ)
  exact h.2

end ModuleCat
