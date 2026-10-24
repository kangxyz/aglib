/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.TrivSqZeroExt
public import Mathlib.RingTheory.DualNumber
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Focused consumer of local and Noetherian trivial square-zero extensions: `L[ε]` and
`L[ε, ε'] = L ⊕ L²` over a field `L`, with axiom guards. -/

@[expose] public section

variable (L : Type*) [Field L]

example : IsLocalRing (TrivSqZeroExt L (L × L)) := inferInstance

example : IsNoetherianRing (TrivSqZeroExt L (L × L)) := inferInstance

example : IsNoetherianRing (DualNumber L) := inferInstance

example : IsLocalHom (TrivSqZeroExt.fstHom L L (L × L)) := inferInstance

/--
info: 'TrivSqZeroExt.isLocalRing' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TrivSqZeroExt.isLocalRing

/--
info: 'TrivSqZeroExt.isNoetherianRing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TrivSqZeroExt.isNoetherianRing
