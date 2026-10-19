/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.PullbackSquare

/-! Focused consumer of flatness of a base change through an intermediate Cartesian square and of
its locality on the test scheme, with axiom guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

example {X S Y P T : Scheme.{u}} {p : X ⟶ S} {j : Y ⟶ S} {a : P ⟶ X} {b : P ⟶ Y}
    (hsq : IsPullback a b p j) (M : X.Modules) [M.IsQuasicoherent] (g' : T ⟶ Y) :
    Scheme.Modules.relativeFlat (pullback.snd p (g' ≫ j))
        ((Scheme.Modules.pullback (pullback.fst p (g' ≫ j))).obj M) ↔
      Scheme.Modules.relativeFlat (pullback.snd b g')
        ((Scheme.Modules.pullback (pullback.fst b g')).obj ((Scheme.Modules.pullback a).obj M)) :=
  Scheme.Modules.relativeFlat_pullback_comp_iff_of_isPullback hsq M g'


/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_pullback_comp_iff_of_isPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_pullback_comp_iff_of_isPullback

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_pullback_snd_opensι' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_pullback_snd_opensι

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_pullback_snd_of_forall_opens' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_pullback_snd_of_forall_opens

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_iff_of_isPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_iff_of_isPullback
