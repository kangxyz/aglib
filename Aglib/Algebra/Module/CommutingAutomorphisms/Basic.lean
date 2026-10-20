/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.LinearAlgebra.Prod

/-! Finite projective modules with two actual commuting automorphisms, their
intertwining isomorphisms, direct sums, rank-one pairs and coordinate exchange.
Extracted from historical Grayson.Basic at e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7;
no Grayson relation or quotient is included. -/
/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/Basic.lean` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`9cf4bd6e9f1839fc99a833ecda410d7a7d78a0a82d183dcadd6f6c489a938fe4`.
-/

@[expose] public section

noncomputable section
namespace Module.CommutingAutomorphisms

universe u v

/-- A finite projective module equipped with two commuting automorphisms.
The carrier is in the same universe as the ring, as are the tensor products
used for extension of scalars. -/
structure Object (R : Type u) [CommRing R] where
  /-- The underlying finite projective module type. -/
  carrier : Type u
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module R carrier]
  [instFinite : Module.Finite R carrier]
  [instProjective : Module.Projective R carrier]
  /-- The first distinguished linear automorphism. -/
  a : carrier ≃ₗ[R] carrier
  /-- The second distinguished linear automorphism, commuting with the first. -/
  b : carrier ≃ₗ[R] carrier
  commute : ∀ x, a (b x) = b (a x)

attribute [instance] Object.instAddCommGroup Object.instModule
  Object.instFinite Object.instProjective

variable {R : Type u} [CommRing R]

namespace Object

/-- An isomorphism of the actual modules intertwining both automorphisms. -/
structure Iso (X Y : Object R) where
  /-- The underlying linear equivalence intertwining both distinguished automorphisms. -/
  linearEquiv : X.carrier ≃ₗ[R] Y.carrier
  commute_a : ∀ x, linearEquiv (X.a x) = Y.a (linearEquiv x)
  commute_b : ∀ x, linearEquiv (X.b x) = Y.b (linearEquiv x)

/-- The identity is an intertwining isomorphism. -/
def Iso.refl (X : Object R) : Iso X X where
  linearEquiv := LinearEquiv.refl R X.carrier
  commute_a _ := rfl
  commute_b _ := rfl

/-- The inverse of an intertwining isomorphism. -/
def Iso.symm {X Y : Object R} (e : Iso X Y) : Iso Y X where
  linearEquiv := e.linearEquiv.symm
  commute_a x := by
    apply e.linearEquiv.injective
    simpa using (e.commute_a (e.linearEquiv.symm x)).symm
  commute_b x := by
    apply e.linearEquiv.injective
    simpa using (e.commute_b (e.linearEquiv.symm x)).symm

/-- Composition of intertwining isomorphisms. -/
def Iso.trans {X Y Z : Object R} (e : Iso X Y) (f : Iso Y Z) : Iso X Z where
  linearEquiv := e.linearEquiv.trans f.linearEquiv
  commute_a x := by
    change f.linearEquiv (e.linearEquiv (X.a x)) = Z.a (f.linearEquiv (e.linearEquiv x))
    rw [e.commute_a, f.commute_a]
  commute_b x := by
    change f.linearEquiv (e.linearEquiv (X.b x)) = Z.b (f.linearEquiv (e.linearEquiv x))
    rw [e.commute_b, f.commute_b]

/-- Direct sum is the actual product module, with diagonal automorphisms. -/
abbrev sum (X Y : Object R) : Object R where
  carrier := X.carrier × Y.carrier
  a := X.a.prodCongr Y.a
  b := X.b.prodCongr Y.b
  commute x := by
    apply Prod.ext
    · exact X.commute x.1
    · exact Y.commute x.2

/-- Build an object from a finite projective module and commuting automorphisms. -/
def ofModule (P : Type u) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (a b : P ≃ₗ[R] P) (commute : ∀ x, a (b x) = b (a x)) : Object R where
  carrier := P
  a := a
  b := b
  commute := commute

/-- The rank-one object associated to a pair of units. These are objects of
reduced split K₀; no multiplicativity or Steinberg relation is asserted here. -/
abbrev unitPair (a b : Rˣ) : Object R where
  carrier := R
  a := LinearEquiv.smulOfUnit a
  b := LinearEquiv.smulOfUnit b
  commute x := by
    change (a : R) * ((b : R) * x) = (b : R) * ((a : R) * x)
    exact mul_left_comm _ _ _

/-- Exchange the two commuting coordinates. -/
def swap (X : Object R) : Object R where
  carrier := X.carrier
  a := X.b
  b := X.a
  commute x := (X.commute x).symm

@[simp] theorem swap_swap (X : Object R) : X.swap.swap = X := rfl

@[simp] theorem swap_sum (X Y : Object R) : (X.sum Y).swap = X.swap.sum Y.swap := rfl

/-- Intertwining isomorphisms are preserved by exchanging coordinates. -/
def Iso.swap {X Y : Object R} (e : Iso X Y) : Iso X.swap Y.swap where
  linearEquiv := e.linearEquiv
  commute_a := e.commute_b
  commute_b := e.commute_a

@[simp] theorem swap_unitPair (a b : Rˣ) : (unitPair a b).swap = unitPair b a := rfl

end Object

end Module.CommutingAutomorphisms
