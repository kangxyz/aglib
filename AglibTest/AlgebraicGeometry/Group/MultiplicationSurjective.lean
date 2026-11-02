/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.MultiplicationSurjective

/-!
# Consumer checks for `Aglib.AlgebraicGeometry.Group.MultiplicationSurjective`

Multiplication by `n` on a proper connected group scheme over an algebraically closed field with
finite `k`-point fibres: values on `k`-points and at the unit, properness, finiteness,
surjectivity and divisibility of the `k`-points; axiom guards.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.Group.Multiplication
open scoped CategoryTheory.MonObj

universe u

namespace AglibTest.GroupMultiplicationSurjective

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]

/-- On `k`-points, `[n]` is the `n`-th power, and it fixes the unit point. -/
example (n : ℕ) (p : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
    ((𝟙 G) ^ n).left (p.left (IsLocalRing.closedPoint k)) =
        (p ^ n).left (IsLocalRing.closedPoint k) ∧
      ((𝟙 G) ^ n).left (unitPoint G) = unitPoint G :=
  ⟨multiplication_left_apply_point G n p, multiplication_left_apply_unitPoint G n⟩

/-- `[n]` is proper when `G` is proper over `k`. -/
example [IsProper G.hom] (n : ℕ) : IsProper ((𝟙 G) ^ n).left :=
  multiplication_isProper G n

/-- Fibres of `[n]` through closed points are finite when the `k`-point fibres are. -/
example [IsAlgClosed k] [LocallyOfFiniteType G.hom] (n : ℕ)
    (hfin : ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ G, {p | p ^ n = y}.Finite) (x : G.left)
    (hx : IsClosed {x}) : (((𝟙 G) ^ n).left ⁻¹' {((𝟙 G) ^ n).left x}).Finite :=
  multiplication_finite_preimage_singleton_of_isClosed_of_finite_setOf_pow_eq_of_isAlgClosed G n
    hfin x hx

/-- For a proper connected group scheme over an algebraically closed field with finite `k`-point
fibres, `[n]` is finite and surjective and every `k`-point is an `n`-th power. -/
example [IsAlgClosed k] [IsProper G.hom] [ConnectedSpace G.left] (n : ℕ)
    (hfin : ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ G, {p | p ^ n = y}.Finite) :
    IsFinite ((𝟙 G) ^ n).left ∧ Surjective ((𝟙 G) ^ n).left ∧
      ∀ y : 𝟙_ (Over (Spec (.of k))) ⟶ G, ∃ p, p ^ n = y :=
  ⟨multiplication_isFinite_of_finite_setOf_pow_eq_of_isAlgClosed G n hfin,
    multiplication_surjective_of_finite_setOf_pow_eq_of_isAlgClosed G n hfin,
    exists_pow_eq_of_finite_setOf_pow_eq_of_isAlgClosed G n hfin⟩

/--
info: 'AlgebraicGeometry.Scheme.Group.Multiplication.multiplication_left_apply_point' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.Multiplication.multiplication_left_apply_point

/--
info: 'AlgebraicGeometry.Scheme.Group.Multiplication.multiplication_left_apply_unitPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.Multiplication.multiplication_left_apply_unitPoint

/--
info: 'AlgebraicGeometry.Scheme.Group.Multiplication.multiplication_isProper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.Multiplication.multiplication_isProper

/--
info: 'AlgebraicGeometry.Scheme.Group.Multiplication.multiplication_finite_preimage_singleton_of_isClosed_of_finite_setOf_pow_eq_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.Multiplication.multiplication_finite_preimage_singleton_of_isClosed_of_finite_setOf_pow_eq_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.Group.Multiplication.multiplication_isFinite_of_finite_setOf_pow_eq_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.Multiplication.multiplication_isFinite_of_finite_setOf_pow_eq_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.Group.Multiplication.multiplication_surjective_of_finite_setOf_pow_eq_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.Multiplication.multiplication_surjective_of_finite_setOf_pow_eq_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.Group.Multiplication.exists_pow_eq_of_finite_setOf_pow_eq_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.Multiplication.exists_pow_eq_of_finite_setOf_pow_eq_of_isAlgClosed

end AglibTest.GroupMultiplicationSurjective
