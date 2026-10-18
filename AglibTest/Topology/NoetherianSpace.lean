/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Topology.NoetherianSpace
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-! Focused consumer of joint local constancy of families of locally constant functions on a
Noetherian space, with an axiom guard. -/

@[expose] public section

/-- On the prime spectrum of a Noetherian ring, a `ℤ`-indexed family of locally constant integer
functions is jointly locally constant. -/
example {A : Type*} [CommRing A] [IsNoetherianRing A] {g : ℤ → PrimeSpectrum A → ℤ}
    (hg : ∀ m, IsLocallyConstant (g m)) : IsLocallyConstant (fun s m => g m s) :=
  TopologicalSpace.NoetherianSpace.isLocallyConstant_pi hg

/--
info: 'TopologicalSpace.NoetherianSpace.isLocallyConstant_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TopologicalSpace.NoetherianSpace.isLocallyConstant_pi

/--
info: 'TopologicalSpace.NoetherianSpace.finite_range_of_isIrreducible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TopologicalSpace.NoetherianSpace.finite_range_of_isIrreducible
