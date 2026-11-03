/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Normal.Frames

/-!
# Pullback of an original line with the original centre-ideal dual twist

This is the original tensor line on the same canonical blowup. Its single
construction is independent of a choice of generators, chart, or trace map.
-/

@[expose] public noncomputable section

open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

variable {R : Type u} [CommRing R] (I : Ideal R)
  (L : Invertible.LineBundle (Spec (.of R)))

/-- The original pulled-back line tensored with the dual of the actual centre ideal. -/
def centreTwistedPullbackLine : Invertible.LineBundle (canonicalBlowup I) :=
  Invertible.tensorLineBundle (canonicalBlowup I)
    (Invertible.pullbackLineBundle (blowdown I) L)
    (Invertible.dualLineBundle (canonicalBlowup I) (centreIdealLine I))

/-- The underlying module is the original tensor module, with the original pullback action. -/
theorem centreTwistedPullbackLine_val :
    (centreTwistedPullbackLine I L).val =
      tensorSheaf (canonicalBlowup I) ((pullback (blowdown I)).obj L.val)
        (Invertible.dualLineBundle (canonicalBlowup I) (centreIdealLine I)).val := rfl

end AlgebraicGeometry.Scheme.Blowup.RegularPoint
