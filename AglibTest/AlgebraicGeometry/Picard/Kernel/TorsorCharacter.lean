/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Kernel.TorsorCharacter

/-! Axiom boundary for the actual original construction. -/

open AlgebraicGeometry.Scheme.Modules.TrivializedDescent

/--
info: 'AlgebraicGeometry.Scheme.Modules.TrivializedDescent.descendFrameIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms descendFrameIso
