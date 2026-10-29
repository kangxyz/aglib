/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.ClosedPointFibres

/-!
# Consumer checks for `Aglib.AlgebraicGeometry.Morphisms.Finite.ClosedPointFibres`

Finite closed subsets of Jacobson spaces, and local quasi-finiteness and finiteness from finite
fibres through closed points, for schemes locally of finite type over a field; axiom guards.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AglibTest.MorphismsFiniteClosedPointFibres

/-- A closed subset of a Jacobson space with finitely many closed points is finite. -/
example {X : Type*} [TopologicalSpace X] [JacobsonSpace X] {Z : Set X} (hZ : IsClosed Z)
    (h : (Z ∩ closedPoints X).Finite) : Z.Finite :=
  JacobsonSpace.finite_of_isClosed_of_finite_inter_closedPoints hZ h

/-- Over a field: a morphism from a scheme locally of finite type over `k`, with finite fibres
through closed points, is locally quasi-finite. -/
example {k : Type u} [Field k] {X Y : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : ∀ x : X, IsClosed {x} → (f ⁻¹' {f x}).Finite) : LocallyQuasiFinite f :=
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  .of_finite_preimage_singleton_of_isClosed_of_jacobsonSpace f hf

/-- Over a field: a proper morphism with finite fibres through closed points is finite. -/
example {k : Type u} [Field k] {X Y : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [IsProper f]
    (hf : ∀ x : X, IsClosed {x} → (f ⁻¹' {f x}).Finite) : IsFinite f :=
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  .of_isProper_of_finite_preimage_singleton_of_isClosed_of_jacobsonSpace f hf

/--
info: 'JacobsonSpace.finite_of_isClosed_of_finite_inter_closedPoints' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms JacobsonSpace.finite_of_isClosed_of_finite_inter_closedPoints

/--
info: 'AlgebraicGeometry.LocallyQuasiFinite.of_finite_preimage_singleton_of_isClosed_of_jacobsonSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.LocallyQuasiFinite.of_finite_preimage_singleton_of_isClosed_of_jacobsonSpace

/--
info: 'AlgebraicGeometry.IsFinite.of_isProper_of_finite_preimage_singleton_of_isClosed_of_jacobsonSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.IsFinite.of_isProper_of_finite_preimage_singleton_of_isClosed_of_jacobsonSpace

end AglibTest.MorphismsFiniteClosedPointFibres
