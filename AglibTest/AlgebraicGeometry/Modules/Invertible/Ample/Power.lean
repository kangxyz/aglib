/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Ample.Power

/-! Positive-power descent keeps the original bundle, with no separation assumption. -/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules.Invertible

universe u

example {X : Scheme.{u}} (L : LineBundle X) (n : ℕ) (hn : 0 < n)
    (h : (tensorPowerLineBundle X L n).IsAmple) : L.IsAmple :=
  LineBundle.IsAmple.of_tensorPower L n hn h

end

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.LineBundle.IsAmple.of_tensorPower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Invertible.LineBundle.IsAmple.of_tensorPower
