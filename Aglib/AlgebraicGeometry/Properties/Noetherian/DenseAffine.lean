/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.DenseAffine

/-!
# Compatibility import for dense affine neighborhoods

The sole implementation belongs to `Properties.DenseAffine`: its primitive
statements require finitely many irreducible components, not Noetherianity.
This former location retains all native `Scheme` declaration names through
the public import, including the Noetherian finite-cover corollary.
-/
