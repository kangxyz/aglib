/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Properties.Noetherian.Coproduct

/-! Focused consumer of locally Noetherian disjoint unions and the disjoint union of locally
Noetherian test schemes, with axiom guards. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- A disjoint union of locally Noetherian schemes, indexed by a type in any universe, is locally
Noetherian. -/
example {σ : Type} (g : σ → Scheme.{u}) [∀ j, IsLocallyNoetherian (g j)] :
    IsLocallyNoetherian (∐ g) :=
  inferInstance

/-- The disjoint union of locally Noetherian test schemes has the induced structure morphism, and
its inclusions are the coprojections. -/
example {S : Scheme.{u}} {σ : Type u} (H : σ → Scheme.LocallyNoetherianOver S) (j : σ) :
    (Scheme.LocallyNoetherianOver.sigma H).obj.hom = Sigma.desc (fun j => (H j).obj.hom) ∧
      (Scheme.LocallyNoetherianOver.sigmaι H j).hom.left = Sigma.ι (fun j => (H j).obj.left) j :=
  ⟨rfl, rfl⟩

/--
info: 'AlgebraicGeometry.isLocallyNoetherian_sigma' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.isLocallyNoetherian_sigma

/--
info: 'AlgebraicGeometry.Scheme.LocallyNoetherianOver.sigma' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocallyNoetherianOver.sigma
