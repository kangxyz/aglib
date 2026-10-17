/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Grassmannian.BaseChangeFormula

/-!
# The supplied base-change formula

Instance search finds `BaseChangeMkQFormula` for the coordinate modules of the charts, so the
Grassmannian results stated under that premise apply unconditionally.
-/

@[expose] public section

universe u

example (R : Type u) [CommRing R] (n : ℕ) :
    Module.Grassmannian.BaseChangeMkQFormula.{u, u, u} R (Fin n → R) := inferInstance

/-- info: 'Module.Grassmannian.baseChangeMkQFormula' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Module.Grassmannian.baseChangeMkQFormula
