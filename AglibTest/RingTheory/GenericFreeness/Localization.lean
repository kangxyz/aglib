/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.GenericFreeness.Localization

/-! Focused consumer of the local form of generic flatness (plan row F12): flatness over `A`
of the localizations `M_P` at primes of `B` not containing the chosen denominator. -/

@[expose] public section

example (A B M : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B]
    [Algebra A B] [Algebra.FiniteType A B] [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M] :
    ∃ a : A, a ≠ 0 ∧ ∀ (P : Ideal B) [P.IsPrime], algebraMap A B a ∉ P →
      Module.Flat A (LocalizedModule P.primeCompl M) :=
  Module.Finite.exists_ne_zero_flat_localizedModule_primeCompl (B := B) M

/--
info: 'Module.Finite.exists_ne_zero_flat_localizedModule_primeCompl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Module.Finite.exists_ne_zero_flat_localizedModule_primeCompl

/--
info: 'Module.flat_of_isLocalizedModule_of_flat_localizedModule_away' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Module.flat_of_isLocalizedModule_of_flat_localizedModule_away

/--
info: 'Module.Flat.of_isLocalizedModule_of_isScalarTower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Module.Flat.of_isLocalizedModule_of_isScalarTower
