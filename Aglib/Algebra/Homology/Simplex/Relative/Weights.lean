/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Endpoints
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.FiniteCoordinates
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Trace

/-!
# The original Laurent tuple complex and its actual weight cohomology

The native coordinate Laurent tuple complex is canonically the actual
coproduct of its unchanged relative-simplex weight complexes. The maps retain
the original graded restrictions, scalar coefficients and alternating signs.
Exact native coproducts and the supportwise relative-simplex calculation give
finite free native homology on `Fin (n + 1)`, in degrees zero and `n` only.
See the focused guide `Relative/Weights/README.md` for hypotheses and interfaces.
-/
