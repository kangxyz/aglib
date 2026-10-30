/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Module.ZMod.PerfectPairing

/-!
# Tests for the native module-duality provider

The examples exercise the actual maps and hypotheses; the guards preserve the
approved transitive axiom boundary for every new public declaration.
-/

@[expose] public noncomputable section

/-- Equal cardinality and one injective adjoint suffice even for composite coefficients. -/
example {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod 6) M] [Module (ZMod 6) N] [Finite M] [Finite N]
    (B : M →ₗ[ZMod 6] N →ₗ[ZMod 6] ZMod 6) (hB : Function.Injective B)
    (hcard : Nat.card M = Nat.card N) : B.IsPerfPair :=
  ZMod.isPerfPair_of_injective_of_natCard_eq 6 B hB hcard

/-- info: 'ZMod.isPerfPair_iff_bijective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.isPerfPair_iff_bijective

/-- info: 'ZMod.isPerfPair_iff_flip_bijective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.isPerfPair_iff_flip_bijective

/-- info: 'ZMod.isPerfPair_of_injective_of_natCard_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.isPerfPair_of_injective_of_natCard_eq

/-- info: 'ZMod.isPerfPair_of_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.isPerfPair_of_injective

/-- info: 'ZMod.natCard_eq_of_isPerfPair' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ZMod.natCard_eq_of_isPerfPair
