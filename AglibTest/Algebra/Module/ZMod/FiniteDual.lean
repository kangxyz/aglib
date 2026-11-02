/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Module.ZMod.FiniteDual

/-!
# Tests for the native module-duality provider

The examples exercise the actual maps and hypotheses; the guards preserve the
approved transitive axiom boundary for every new public declaration.
-/

@[expose] public noncomputable section

/-- The nonfree quotient of ZMod four by twice the ring has the expected dual cardinality. -/
example : Nat.card (Module.Dual (ZMod 4) (ZMod 4 ⧸ Ideal.span {(2 : ZMod 4)})) =
    Nat.card (ZMod 4 ⧸ Ideal.span {(2 : ZMod 4)}) :=
  ZMod.natCard_dual 4 _

/-- Biduality uses the actual native evaluation and preserves its values. -/
example (n : ℕ) [NeZero n] (M : Type*) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (x : M) (f : Module.Dual (ZMod n) M) :
    letI := ZMod.isReflexive_of_finite n M
    Module.evalEquiv (ZMod n) M x f = f x := rfl

/-- info: 'ZMod.finiteDual' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.finiteDual

/-- info: 'ZMod.natCard_dual' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.natCard_dual

/-- info: 'ZMod.exists_dual_apply_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.exists_dual_apply_ne_zero

/-- info: 'ZMod.dual_eval_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.dual_eval_injective

/-- info: 'ZMod.dual_eval_bijective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.dual_eval_bijective

/-- info: 'ZMod.isReflexive_of_finite' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.isReflexive_of_finite
