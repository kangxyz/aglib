/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing.Nonzero

/-! The nonzero-section supplier only requires reducedness. -/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules.Invertible

universe u

example {X : Scheme.{u}} [IsReduced X] (L : LineBundle X)
    (s : Γ(L.val, ⊤)) (hs : s ≠ 0) : (nonvanishingOpen L s : Set X).Nonempty :=
  nonempty_nonvanishingOpen_of_ne_zero L s hs

end

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.nonempty_nonvanishingOpen_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Invertible.nonempty_nonvanishingOpen_of_ne_zero
