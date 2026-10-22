/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-!
# Pulling back a lifted finite-etale cover through an actual square

A cover which lifts on one fibre still lifts after a specified commutative
base-change square. The residue-base map need not be an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

variable {X Z K L : Scheme.{u}} (a : X ⟶ Z) (i : K ⟶ X)
  (j : L ⟶ Z) (g : K ⟶ L) (h : i ≫ a = g ≫ j)

include h

/-- Pull an actual lifted cover through the given commutative square, retaining
its isomorphism with the specified pullback of the original fibre cover. -/
theorem exists_cover_pullback_of_square [(baseChange j).EssSurj] (C : FiniteEtale L) :
    ∃ W : FiniteEtale X, Nonempty ((baseChange i).obj W ≅ (baseChange g).obj C) := by
  let F := baseChange j
  let V := F.objPreimage C
  let e := F.objObjPreimageIso C
  refine ⟨(baseChange a).obj V, ⟨?_⟩⟩
  exact (baseChangeComp a i).symm.app V ≪≫
    (eqToIso (congrArg baseChange h)).app V ≪≫
      (baseChangeComp j g).app V ≪≫ (baseChange g).mapIso e

end AlgebraicGeometry.Scheme.FiniteEtale
