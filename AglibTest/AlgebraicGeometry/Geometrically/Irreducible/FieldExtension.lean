/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Geometrically.Irreducible.FieldExtension

/-!
# Irreducibility under field extension

The examples restate that irreducibility of field base changes descends along field extensions,
that irreducibility after every algebraically closed extension gives geometric irreducibility, and
guard the axioms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AglibTest.GeometricallyIrreducibleFieldExtension

open AlgebraicGeometry AlgebraicGeometry.Scheme.Geometrically

variable {k : Type u} [Field k] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of k))

/-- Irreducibility over an algebraic closure of an extension gives irreducibility over the
extension. -/
example (K : Type u) [Field K] [Algebra k K]
    [IrreducibleSpace (pullback q
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure K)))) : Scheme.{u})] :
    IrreducibleSpace (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) :=
  irreducibleSpace_pullback_of_irreducibleSpace_pullback_of_isScalarTower q K (AlgebraicClosure K)

/-- The criterion for geometric irreducibility. -/
theorem criterion
    (h : ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
      IrreducibleSpace (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) :
    GeometricallyIrreducible q :=
  geometricallyIrreducible_of_forall_isAlgClosed q h

/-- A geometrically irreducible scheme over a field is irreducible. -/
example [Nonempty Y]
    (h : ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
      IrreducibleSpace (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) :
    IrreducibleSpace Y :=
  have := criterion q h
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton q

/-- info: 'AlgebraicGeometry.Scheme.Geometrically.irreducibleSpace_pullback_of_irreducibleSpace_pullback_of_isScalarTower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms irreducibleSpace_pullback_of_irreducibleSpace_pullback_of_isScalarTower

/-- info:
'AlgebraicGeometry.Scheme.Geometrically.geometricallyIrreducible_of_forall_isAlgClosed' depends
on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms geometricallyIrreducible_of_forall_isAlgClosed

end AglibTest.GeometricallyIrreducibleFieldExtension
