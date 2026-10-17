/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.GenericFreeness.Noetherian

/-! Focused consumer of generic freeness (plan row F12; Stacks 051R, Nitsure Lemma 4.1): for a
Noetherian domain `A`, a finitely generated `A`-algebra `B` and a finite `B`-module `M`, the
localization `LocalizedModule.Away a M` is free over `Localization.Away a` for some `a ≠ 0`. -/

@[expose] public section

example (A B M : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B]
    [Algebra A B] [Algebra.FiniteType A B] [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M] :
    ∃ a : A, a ≠ 0 ∧ Module.Free (Localization.Away a) (LocalizedModule.Away a M) :=
  Module.Finite.exists_ne_zero_free_localizedModule_away (B := B) M

example (A B M : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B]
    [Algebra A B] [Algebra.FiniteType A B] [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M] :
    ∃ a : A, a ≠ 0 ∧ Module.Flat (Localization.Away a) (LocalizedModule.Away a M) :=
  Module.Finite.exists_ne_zero_flat_localizedModule_away (B := B) M

/-- The integral structure of an abelian group is the one used: a finite module over
`ℤ[x, y]` has a nonzero integer `a` with `M[1/a]` free over `ℤ[1/a]`. -/
example (M : Type) [AddCommGroup M] [Module (MvPolynomial (Fin 2) ℤ) M]
    [Module.Finite (MvPolynomial (Fin 2) ℤ) M] :
    ∃ a : ℤ, a ≠ 0 ∧ Module.Free (Localization.Away a) (LocalizedModule.Away a M) :=
  Module.Finite.exists_ne_zero_free_localizedModule_away (B := MvPolynomial (Fin 2) ℤ) M

/--
info: 'Module.Finite.exists_ne_zero_free_localizedModule_away' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Module.Finite.exists_ne_zero_free_localizedModule_away

/--
info: 'Module.Finite.exists_ne_zero_flat_localizedModule_away' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Module.Finite.exists_ne_zero_flat_localizedModule_away

/--
info: 'Module.Finite.exists_free_localizedModule_away_of_isNoetherianRing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Module.Finite.exists_free_localizedModule_away_of_isNoetherianRing
