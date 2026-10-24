/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Separated.Cover

/-!
# Consumer checks for separatedness from a cover by separated opens

The trivial cover recovers a separated morphism, and the strata form applies to opens indexed by
a type and an integer level, monotone in the level and disjoint for distinct indices (Kleiman,
*The Picard scheme*, arXiv:math/0504020v1, proof of Thm 4.8, p. 28).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AglibTest.SeparatedCover

variable {P S : Scheme.{u}} (f : P ⟶ S)

/-- A separated morphism, through the cover by `⊤`. -/
example [IsSeparated f] : IsSeparated f :=
  isSeparated_of_cover_of_directed f (fun _ : PUnit.{1} => ⊤) (by simp)
    (fun _ => inferInstance) fun _ _ => ⟨PUnit.unit, le_rfl, le_rfl⟩

/-- The strata form with integer levels. -/
example {ι : Type*} (U : ι → ℤ → P.Opens) (hU : ⨆ i, ⨆ m, U i m = ⊤)
    (hsep : ∀ i m, IsSeparated ((U i m).ι ≫ f)) (hmono : ∀ i, Monotone (U i))
    (hdisj : ∀ i i' m m', i ≠ i' → Disjoint (U i m) (U i' m')) : IsSeparated f :=
  isSeparated_of_cover_of_disjoint_of_monotone f U hU hsep hmono hdisj

/-- Pairwise disjoint separated opens. -/
example {ι : Type*} (U : ι → P.Opens) (hU : ⨆ i, U i = ⊤)
    (hsep : ∀ i, IsSeparated ((U i).ι ≫ f)) (hdisj : Pairwise (Function.onFun Disjoint U)) :
    IsSeparated f :=
  isSeparated_of_cover_of_pairwise_disjoint f U hU hsep hdisj

/--
info: 'AlgebraicGeometry.isSeparated_of_cover_of_disjoint_or_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isSeparated_of_cover_of_disjoint_or_le

/--
info: 'AlgebraicGeometry.isSeparated_of_cover_of_disjoint_of_monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms isSeparated_of_cover_of_disjoint_of_monotone

end AglibTest.SeparatedCover
