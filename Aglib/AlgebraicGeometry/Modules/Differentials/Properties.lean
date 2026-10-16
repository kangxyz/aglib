/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.SmoothRank

/-!
# Differential properties from the actual proofs

Compatibility import for the native smooth-rank and etale pullback theorems.
`SmoothRank` supplies actual local bases of the original differential sheaf;
`EtalePullback` supplies invertibility of its canonical pullback map.
The former global theorem-family premises are retired. Focused consumers
should import those two owning leaves directly.
-/
