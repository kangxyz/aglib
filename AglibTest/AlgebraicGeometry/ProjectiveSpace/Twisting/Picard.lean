/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting.Picard

/-! Integer twist classes use the same native O(1) on arbitrary projective space. -/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

example (R : Type u) [CommRing R] (I : Type u) (d : ℤ) :
    classOf (ProjectiveSpace R I) (twistingLineBundle R I d) =
      d • classOf (ProjectiveSpace R I) (twistingLineBundle R I 1) :=
  twistClassHom_eq_zsmul R I d

end
