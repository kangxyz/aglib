/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.IdentityComponent.Basic

/-!
# The identity component of a group scheme over a field

The examples restate that the identity component of a group scheme locally of finite type over a
field is open and closed, contains the unit, is geometrically connected, is a group scheme and
has a monoid-morphism inclusion compatible with the unit, multiplication and inverse, and guard
the axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AglibTest.IdentityComponent

open AlgebraicGeometry AlgebraicGeometry.Scheme.Group

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom]

/-- `G⁰` is open and closed and contains the unit point. -/
theorem isClopen_and_mem :
    IsClopen (identityComponent G : Set G.left) ∧ unitPoint G ∈ identityComponent G :=
  ⟨isClopen_identityComponent G, unitPoint_mem_identityComponent G⟩

/-- `G⁰` is geometrically connected over `k`. -/
theorem geometricallyConnected : GeometricallyConnected (identityComponentOver G).hom :=
  inferInstance

/-- `G⁰` is a group scheme, and the inclusion is a monoid morphism. -/
example : GrpObj (identityComponentOver G) := inferInstance

example : IsMonHom (identityComponentι G) := inferInstance

/-- The inclusion is compatible with the multiplication and the inverse. -/
theorem mul_inv_ι :
    μ[identityComponentOver G] ≫ identityComponentι G =
        (identityComponentι G ⊗ₘ identityComponentι G) ≫ μ[G] ∧
      ι[identityComponentOver G] ≫ identityComponentι G = identityComponentι G ≫ ι[G] :=
  ⟨IsMonHom.mul_hom _, identityComponentInv_ι G⟩

/-- Morphisms from connected schemes over `k` through the unit land in `G⁰`. -/
example {T : Over (Spec (.of k))} [ConnectedSpace T.left] (f : T ⟶ G)
    (t : 𝟙_ (Over (Spec (.of k))) ⟶ T) (ht : t ≫ f = η[G]) :
    t ≫ liftIdentityComponent G f (range_subset_identityComponent_of_section G f t ht) ≫
      identityComponentι G = η[G] := by
  simp [ht]

/-- `G⁰` is locally of finite type over `k`, and its inclusion is an open immersion. -/
example : LocallyOfFiniteType (identityComponentOver G).hom := inferInstance

example : IsOpenImmersion (identityComponentι G).left := inferInstance

/-- `G⁰ ×_k G⁰` is connected. -/
example : ConnectedSpace (identityComponentOver G ⊗ identityComponentOver G).left := inferInstance

/-- info: 'AlgebraicGeometry.Scheme.Group.isClosed_identityComponent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isClosed_identityComponent

/-- info: 'AlgebraicGeometry.Scheme.Group.geometricallyConnected_identityComponentOver' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms geometricallyConnected_identityComponentOver

/-- info: 'AlgebraicGeometry.Scheme.Group.grpObjIdentityComponentOver' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms grpObjIdentityComponentOver

/-- info: 'AlgebraicGeometry.Scheme.Group.isMonHom_identityComponentι' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isMonHom_identityComponentι

/-- info: 'AglibTest.IdentityComponent.mul_inv_ι' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mul_inv_ι

end AglibTest.IdentityComponent
