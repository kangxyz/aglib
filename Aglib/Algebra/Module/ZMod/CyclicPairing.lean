/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Module.ZMod.PerfectPairing

/-!
# Perfectness from evaluation on a cyclic generator

For an actual ZMod bilinear pairing, a generator in one variable reduces
perfectness to bijectivity of its evaluation in the other. The statement uses
the original `LinearMap.IsPerfPair` and the existing finite ZMod duality; it
does not assert that other finite ZMod modules are free.
-/

@[expose] public noncomputable section

namespace ZMod

variable (n : ℕ) [NeZero n]
  {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module (ZMod n) M] [Module (ZMod n) N]

/-- Evaluation on an actual scalar generator detects perfectness. -/
theorem isPerfPair_of_bijective_eval_generator
    (B : M →ₗ[ZMod n] N →ₗ[ZMod n] ZMod n) (y : N)
    (hy : Function.Surjective (fun a : ZMod n => a • y))
    (hB : Function.Bijective (fun x => B x y)) : B.IsPerfPair := by
  let : Finite N := Finite.of_surjective _ hy
  apply (isPerfPair_iff_bijective n B).mpr
  constructor
  · intro x x' h
    exact hB.injective (DFunLike.congr_fun h y)
  · intro f
    obtain ⟨x, hx⟩ := hB.surjective (f y)
    refine ⟨x, ?_⟩
    ext z
    obtain ⟨a, rfl⟩ := hy z
    simp only [map_smul, hx]

/-- When both original modules vanish, their original bilinear pairing is perfect. -/
theorem isPerfPair_of_subsingleton [Subsingleton M] [Subsingleton N]
    (B : M →ₗ[ZMod n] N →ₗ[ZMod n] ZMod n) : B.IsPerfPair := by
  apply (isPerfPair_iff_bijective n B).mpr
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun f => ⟨0, Subsingleton.elim _ _⟩⟩

end ZMod
