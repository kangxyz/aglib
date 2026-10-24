/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOverBaseChange

/-! Focused consumer of locally Noetherian test schemes along a change of base, with axiom
guards. -/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

universe u

variable {S S' : Scheme.{u}} (g : S' ⟶ S)

/-- `Over.map g` keeps the underlying scheme of a locally Noetherian test scheme. -/
example (T : Scheme.LocallyNoetherianOver S') :
    ((Scheme.LocallyNoetherianOver.map g).obj T).obj.left = T.obj.left ∧
      ((Scheme.LocallyNoetherianOver.map g).obj T).obj.hom = T.obj.hom ≫ g :=
  ⟨rfl, rfl⟩

/-- `P ×_S S'` is a locally Noetherian `S'`-scheme, locally of finite type over `S'`. -/
example [IsLocallyNoetherian S'] (P : Scheme.LocallyNoetherianOver S)
    [LocallyOfFiniteType P.obj.hom] :
    (Scheme.LocallyNoetherianOver.baseChange g P).obj.left = pullback P.obj.hom g ∧
      LocallyOfFiniteType (Scheme.LocallyNoetherianOver.baseChange g P).obj.hom ∧
      IsLocallyNoetherian (Scheme.LocallyNoetherianOver.baseChange g P).obj.left :=
  ⟨rfl, inferInstance, inferInstance⟩

/--
info: 'AlgebraicGeometry.Scheme.LocallyNoetherianOver.map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.LocallyNoetherianOver.map

/--
info: 'AlgebraicGeometry.Scheme.isLocallyNoetherian_over_pullback_obj_left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.isLocallyNoetherian_over_pullback_obj_left
