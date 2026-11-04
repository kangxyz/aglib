/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.Bidual
public import Aglib.AlgebraicGeometry.Group.CartierDuality.Coordinate.Degree
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.FieldRank

/-!
# The structural rank of the original finite Cartier dual

The same original coordinate Hopf algebra and its native linear dual have
equal dimension. The existing structural affine comparisons identify this
with finite-scheme degree and native locally free rank. No replacement
coordinate algebra or reducedness, characteristic or etaleness condition is
introduced. The current consumer is duality of original multiplication kernels.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.OverField
open scoped Module.Dual.FiniteDual

universe u

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

variable {k : Type u} [Field k]

/-- Finite Cartier duality preserves the actual structural finite-scheme degree. -/
theorem finiteSchemeDegree_dualGroup (G : Grp (FScheme k))
    [IsFinite G.X.hom] [IsCommMonObj G.X] :
    Hom.finiteSchemeDegree k (dualGroup G).X.hom = Hom.finiteSchemeDegree k G.X.hom := by
  rw [finiteSchemeDegree_eq_finrank_coordinateHopf,
    finiteSchemeDegree_eq_finrank_coordinateHopf]
  exact (CommHopfAlgCat.ofIso (dualCoordinateIso G)).toLinearEquiv.finrank_eq.symm.trans
    (Subspace.dual_finrank_eq (K := k) (V := coordinateHopf G))

/-- The original Cartier dual has exactly the same native locally free rank. -/
theorem dualGroup_hasLocallyFreeRank_iff (G : Grp (FScheme k))
    [IsFinite G.X.hom] [IsCommMonObj G.X] (n : ℕ) :
    Hom.HasLocallyFreeRank (dualGroup G).X.hom n ↔ Hom.HasLocallyFreeRank G.X.hom n := by
  rw [Hom.hasLocallyFreeRank_iff_finiteSchemeDegree_eq,
    Hom.hasLocallyFreeRank_iff_finiteSchemeDegree_eq, finiteSchemeDegree_dualGroup]

end AlgebraicGeometry.Scheme.Group.CartierDuality
