/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Schemes over a field

The actual base scheme and over-category, extracted from
`R5Lab.AlgebraicGeometry.FiniteEtale.PointedCover:55–66` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
No torsor, coefficient group, pointed cover or curve data is included.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.OverField

universe u

variable (F : Type u) [Field F]

/-- The actual base scheme `Spec F`. -/
abbrev Base := Spec (CommRingCat.of F)

/-- The category of schemes and scheme morphisms over `Spec F`. -/
abbrev FScheme := Over (Base F)

end AlgebraicGeometry.Scheme.OverField
