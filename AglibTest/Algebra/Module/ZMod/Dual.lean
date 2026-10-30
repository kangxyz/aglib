/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Module.ZMod.Dual

/-!
# Tests for the native module-duality provider

The examples exercise the actual maps and hypotheses; the guards preserve the
approved transitive axiom boundary for every new public declaration.
-/

@[expose] public noncomputable section

/-- Exactness is on the original precomposition maps, with no finite-module premise. -/
example (n : ℕ) [NeZero n] {M N P : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module (ZMod n) M] [Module (ZMod n) N] [Module (ZMod n) P]
    (f : M →ₗ[ZMod n] N) (g : N →ₗ[ZMod n] P) (hfg : Function.Exact f g)
    (h : Module.Dual (ZMod n) N) :
    h.comp f = 0 ↔ ∃ k : Module.Dual (ZMod n) P, k.comp g = h :=
  ZMod.dualMap_exact n f g hfg h

/-- info: 'ZMod.dualMap_surjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.dualMap_surjective

/-- info: 'ZMod.dualMap_exact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.dualMap_exact

/-- info: 'ZMod.dualMap_shortExact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.dualMap_shortExact
