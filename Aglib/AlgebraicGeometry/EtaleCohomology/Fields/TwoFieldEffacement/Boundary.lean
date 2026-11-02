/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.ClosedPoint

/-! # Closed boundary points for two-field effacement

The scheme-square construction lives in `AlgebraicGeometry.Scheme`. This
compatibility interface retains the original name and all original hypotheses.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

export AlgebraicGeometry.Scheme (exists_closedPoint_outside_of_surjective_square)

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
