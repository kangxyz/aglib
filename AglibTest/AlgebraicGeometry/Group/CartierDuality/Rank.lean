/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.Rank

/-! The native finite Cartier dual retains the original structural rank. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.OverField
open scoped CategoryTheory.MonObj

universe u

example {k : Type u} [Field k] (G : Grp (FScheme k))
    [IsFinite G.X.hom] [IsCommMonObj G.X] (n : ℕ) :
    Scheme.Hom.HasLocallyFreeRank (Scheme.Group.CartierDuality.dualGroup G).X.hom n ↔
      Scheme.Hom.HasLocallyFreeRank G.X.hom n :=
  Scheme.Group.CartierDuality.dualGroup_hasLocallyFreeRank_iff G n
