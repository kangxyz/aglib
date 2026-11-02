/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.Descent

/-! The algebraic descent interface uses the original flat ring maps. -/

@[expose] public section

example : RingHom.CodescendsAlong RingHom.Flat RingHom.FaithfullyFlat :=
  RingHom.Flat.codescendsAlong_faithfullyFlat

end
