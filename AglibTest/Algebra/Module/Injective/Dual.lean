/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Module.Injective.Dual

/-!
# Tests for the native module-duality provider

The examples exercise the actual maps and hypotheses; the guards preserve the
approved transitive axiom boundary for every new public declaration.
-/

@[expose] public noncomputable section

universe u v w t

/-- The original short-exact dual maps allow independent ring and module universes. -/
example {R : Type u} [CommRing R] [Module.Injective R R]
    {M : Type v} {N : Type w} {P : Type t}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Injective g.dualMap ∧ Function.Exact g.dualMap f.dualMap ∧
      Function.Surjective f.dualMap := Module.Injective.dualMap_shortExact f g hf hfg hg

/-- info: 'Module.Injective.dualMap_surjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.Injective.dualMap_surjective

/-- info: 'Module.Injective.dualMap_exact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.Injective.dualMap_exact

/-- info: 'Module.Injective.dualMap_shortExact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Module.Injective.dualMap_shortExact
