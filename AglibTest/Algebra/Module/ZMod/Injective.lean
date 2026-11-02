/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Module.ZMod.Injective

/-!
# Tests for the native module-duality provider

The examples exercise the actual maps and hypotheses; the guards preserve the
approved transitive axiom boundary for every new public declaration.
-/

@[expose] public noncomputable section

/-- Modulus one is included, with its actual zero ring. -/
example : Module.Injective (ZMod 1) (ZMod 1) := ZMod.injective_self 1

/-- Composite modulus six is included without a field instance. -/
example : Module.Injective (ZMod 6) (ZMod 6) := ZMod.injective_self 6

universe u v

/-- Extension does not resize the arbitrary source and target modules. -/
example (n : ℕ) [NeZero n] {M : Type u} {N : Type v}
    [AddCommGroup M] [AddCommGroup N] [Module (ZMod n) M] [Module (ZMod n) N]
    (f : M →ₗ[ZMod n] N) (hf : Function.Injective f) (g : M →ₗ[ZMod n] ZMod n) :
    ∃ h : N →ₗ[ZMod n] ZMod n, h.comp f = g := ZMod.exists_dual_extension n f hf g

/-- info: 'ZMod.baer_self' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.baer_self

/-- info: 'ZMod.injective_self' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.injective_self

/-- info: 'ZMod.exists_dual_extension' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.exists_dual_extension
