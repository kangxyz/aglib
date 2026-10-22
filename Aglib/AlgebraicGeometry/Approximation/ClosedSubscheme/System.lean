/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.Diagrams

/-!
# Closed-diagram comparisons for approximation

The arbitrary closed-over-diagram cone and ideal-supremum constructions live in
`Scheme.ClosedSubscheme`. This compatibility interface retains the approximation
names and the actual original cone maps without a second universal-property proof.
-/

@[expose] public section

namespace AlgebraicGeometry.Approximation.ClosedSubscheme

export AlgebraicGeometry.Scheme.ClosedSubscheme
  (cone cone_π_app_left_hom cone_projection_closed isLimitCone schemeCone
    isLimitSchemeCone idealDiagram idealDiagram_obj_closed diagram_map_closed
    idealCone isLimitIdealCone isLimitIdealSchemeCone)

end AlgebraicGeometry.Approximation.ClosedSubscheme
