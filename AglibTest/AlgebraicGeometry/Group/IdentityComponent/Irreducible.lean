/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.IdentityComponent.Irreducible

/-!
# Irreducibility of the identity component over an algebraically closed field

The examples restate that translations act transitively on closed points of a group scheme
locally of finite type over an algebraically closed field, that such a group scheme is irreducible
when connected, and that its identity component is irreducible, and guard the axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AglibTest.IdentityComponentIrreducible

open AlgebraicGeometry AlgebraicGeometry.Scheme.Group

variable {k : Type u} [Field k] [IsAlgClosed k] (G : Over (Spec (.of k))) [GrpObj G]
  [LocallyOfFiniteType G.hom]

/-- Closed points are values of rational points. -/
example {z : G.left} (hz : IsClosed {z}) :
    ∃ p : 𝟙_ (Over (Spec (.of k))) ⟶ G, p.left (IsLocalRing.closedPoint k) = z :=
  exists_point_left_apply_eq_of_isClosed_of_isAlgClosed G hz

/-- Automorphisms of `G` over `k` act transitively on closed points. -/
theorem transitive {x y : G.left} (hx : IsClosed {x}) (hy : IsClosed {y}) :
    ∃ α : G ≅ G, α.hom.left x = y :=
  exists_iso_hom_left_apply_eq_of_isClosed_of_isAlgClosed G hx hy

/-- A connected group scheme over an algebraically closed field is irreducible. -/
example [ConnectedSpace G.left] : IrreducibleSpace G.left :=
  irreducibleSpace_of_connectedSpace_of_isAlgClosed G

/-- `G⁰` is irreducible over an algebraically closed field. -/
theorem irreducible : IrreducibleSpace (identityComponent G).toScheme :=
  irreducibleSpace_identityComponent_of_isAlgClosed G

/-- info: 'AlgebraicGeometry.Scheme.Group.exists_iso_hom_left_apply_eq_of_isClosed_of_isAlgClosed' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_iso_hom_left_apply_eq_of_isClosed_of_isAlgClosed

/-- info: 'AlgebraicGeometry.Scheme.Group.irreducibleSpace_of_connectedSpace_of_isAlgClosed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms irreducibleSpace_of_connectedSpace_of_isAlgClosed

/-- info: 'AlgebraicGeometry.Scheme.Group.irreducibleSpace_identityComponent_of_isAlgClosed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms irreducibleSpace_identityComponent_of_isAlgClosed

/-- info: 'AglibTest.IdentityComponentIrreducible.irreducible' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms irreducible

end AglibTest.IdentityComponentIrreducible
