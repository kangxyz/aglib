/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Module.ZMod.CyclicPairing

/-! Original-map examples and approved-axiom guards. -/

@[expose] public noncomputable section

/-- Composite coefficients require only an actual generator and bijective evaluation. -/
example {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod 6) M] [Module (ZMod 6) N]
    (B : M →ₗ[ZMod 6] N →ₗ[ZMod 6] ZMod 6) (y : N)
    (hy : Function.Surjective (fun a : ZMod 6 => a • y))
    (hB : Function.Bijective (fun x => B x y)) : B.IsPerfPair :=
  ZMod.isPerfPair_of_bijective_eval_generator 6 B y hy hB

/-- The zero-ring case is included. -/
example {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod 1) M] [Module (ZMod 1) N] [Subsingleton M] [Subsingleton N]
    (B : M →ₗ[ZMod 1] N →ₗ[ZMod 1] ZMod 1) : B.IsPerfPair :=
  ZMod.isPerfPair_of_subsingleton 1 B

/-- info: 'ZMod.isPerfPair_of_bijective_eval_generator' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.isPerfPair_of_bijective_eval_generator

/-- info: 'ZMod.isPerfPair_of_subsingleton' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.isPerfPair_of_subsingleton
