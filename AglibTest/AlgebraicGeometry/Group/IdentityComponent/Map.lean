/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.IdentityComponent.Map

/-! # Component restriction for actual pointed maps, with no separation/properness input -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Scheme.Group
open scoped CategoryTheory.MonObj

universe u

example {k : Type u} [Field k] {G H K : Over (Spec (.of k))}
    [MonObj G] [MonObj H] [MonObj K]
    [LocallyOfFiniteType G.hom] [LocallyOfFiniteType H.hom] [LocallyOfFiniteType K.hom]
    (f : G ⟶ H) (g : H ⟶ K) (hf : η[G] ≫ f = η[H]) (hg : η[H] ≫ g = η[K]) :
    identityComponentMap (f ≫ g) (by rw [← Category.assoc, hf, hg]) =
      identityComponentMap f hf ≫ identityComponentMap g hg :=
  identityComponentMap_comp f g hf hg

example {k : Type u} [Field k] {G H : Over (Spec (.of k))} [GrpObj G] [GrpObj H]
    [LocallyOfFiniteType G.hom] [LocallyOfFiniteType H.hom]
    (f : G ⟶ H) [IsMonHom f] :
    IsMonHom (identityComponentMap f (IsMonHom.one_hom f)) := inferInstance

/--
info: 'AlgebraicGeometry.Scheme.Group.identityComponentMap_comp'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.identityComponentMap_comp
