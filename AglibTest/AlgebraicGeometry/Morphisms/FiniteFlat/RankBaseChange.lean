/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.RankBaseChange

/-! Rank base change uses the actual Cartesian maps and allows nonflat changes of base. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

example {W X T S : Scheme.{u}} (a : W ⟶ X) (b : W ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
    (h : IsPullback a b f g) (r : ℕ) (hf : Scheme.Hom.HasLocallyFreeRank f r) :
    Scheme.Hom.HasLocallyFreeRank b r :=
  Scheme.Hom.hasLocallyFreeRank_of_isPullback a b f g h r hf

end
