/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank

/-!
# Line bundles are the finite locally free sheaves of rank one

`Invertible.IsLocallyRankOne X M` (a local basis with singleton index sets) is equivalent to
`SheafHasRank M 1` (a local basis with index sets equivalent to `Fin 1`):
`Invertible.isLocallyRankOne_iff_sheafHasRank_one`, moved verbatim from
`Modules/Invertible/Formal/Algebraization.lean`.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

/-- Singleton local bases are precisely local bases of displayed rank one. -/
theorem isLocallyRankOne_iff_sheafHasRank_one {X : Scheme.{u}} (M : X.Modules) :
    IsLocallyRankOne X M ↔ SheafHasRank M 1 := by
  constructor
  · rintro ⟨q, hq, h⟩
    exact ⟨q, hq, fun i => ⟨(h i).some.trans (Equiv.ofUnique _ _)⟩⟩
  · rintro ⟨q, hq, h⟩
    exact ⟨q, hq, fun i => ⟨(h i).some.trans (Equiv.ofUnique _ _)⟩⟩

end AlgebraicGeometry.Scheme.Modules.Invertible
