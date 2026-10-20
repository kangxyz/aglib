/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.CommutingAutomorphisms.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/Algebra/Module/Automorphism/Basic.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`9686166959f16ee38639b37804b3379b9e2e945b26b372d521f2bcd6cca2c3fb`.
-/

@[expose] public section

noncomputable section
namespace Module.Automorphism

universe u v

structure Object (R : Type u) [CommRing R] where
  carrier : Type u
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module R carrier]
  [instFinite : Module.Finite R carrier]
  [instProjective : Module.Projective R carrier]
  a : carrier ≃ₗ[R] carrier

attribute [instance] Object.instAddCommGroup Object.instModule
  Object.instFinite Object.instProjective

variable {R : Type u} [CommRing R]

namespace Object

/-- An isomorphism intertwining the automorphism. -/
structure Iso (X Y : Object R) where
  linearEquiv : X.carrier ≃ₗ[R] Y.carrier
  commute_a : ∀ x, linearEquiv (X.a x) = Y.a (linearEquiv x)

/-- The direct sum carries the block-diagonal automorphism. -/
abbrev sum (X Y : Object R) : Object R where
  carrier := X.carrier × Y.carrier
  a := X.a.prodCongr Y.a

/-- A unit acting on the rank-one free module. -/
abbrev unit (a : Rˣ) : Object R where
  carrier := R
  a := LinearEquiv.smulOfUnit a

end Object

namespace Object

open _root_.TensorProduct

/-- The actual tensor product of two weight-one objects. Its automorphisms
act on the first and second factor respectively, hence commute. -/
abbrev tensor (X Y : Object R) : CommutingAutomorphisms.Object R where
  carrier := X.carrier ⊗[R] Y.carrier
  a := TensorProduct.congr X.a (LinearEquiv.refl R Y.carrier)
  b := TensorProduct.congr (LinearEquiv.refl R X.carrier) Y.a
  commute z := by
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x y hx hy => simp [hx, hy]

/-- Tensor products preserve intertwining isomorphisms in both variables. -/
def Iso.tensor {X X' Y Y' : Object R} (e : Iso X X') (f : Iso Y Y') :
    CommutingAutomorphisms.Object.Iso (X.tensor Y) (X'.tensor Y') where
  linearEquiv := TensorProduct.congr e.linearEquiv f.linearEquiv
  commute_a z := by
    dsimp only [Object.tensor, Object.sum, CommutingAutomorphisms.Object.sum]
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp [e.commute_a]
    | add x y hx hy => simp [hx, hy]
  commute_b z := by
    dsimp only [Object.tensor, Object.sum, CommutingAutomorphisms.Object.sum]
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp [f.commute_a]
    | add x y hx hy => simp [hx, hy]

/-- Identity intertwining isomorphism. -/
def Iso.refl (X : Object R) : Iso X X where
  linearEquiv := LinearEquiv.refl R X.carrier
  commute_a _ := rfl

/-- Tensor product distributes over the actual direct sum in the first factor. -/
def tensorSumLeft (X X' Y : Object R) :
    CommutingAutomorphisms.Object.Iso ((X.sum X').tensor Y) ((X.tensor Y).sum (X'.tensor Y)) where
  linearEquiv := TensorProduct.prodLeft R R X.carrier X'.carrier Y.carrier
  commute_a z := by
    dsimp only [Object.tensor, Object.sum, CommutingAutomorphisms.Object.sum]
    induction z using TensorProduct.inductionOn with
    | tmul x y => rcases x with ⟨x, x'⟩; simp
    | add x y hx hy => simp [hx, hy]
  commute_b z := by
    dsimp only [Object.tensor, Object.sum, CommutingAutomorphisms.Object.sum]
    induction z using TensorProduct.inductionOn with
    | tmul x y => rcases x with ⟨x, x'⟩; simp
    | add x y hx hy => simp [hx, hy]

/-- Tensor product distributes over the actual direct sum in the second factor. -/
def tensorSumRight (X Y Y' : Object R) :
    CommutingAutomorphisms.Object.Iso (X.tensor (Y.sum Y')) ((X.tensor Y).sum (X.tensor Y')) where
  linearEquiv := TensorProduct.prodRight R R X.carrier Y.carrier Y'.carrier
  commute_a z := by
    dsimp only [Object.tensor, Object.sum, CommutingAutomorphisms.Object.sum]
    induction z using TensorProduct.inductionOn with
    | tmul x y => rcases y with ⟨y, y'⟩; simp
    | add x y hx hy => simp [hx, hy]
  commute_b z := by
    dsimp only [Object.tensor, Object.sum, CommutingAutomorphisms.Object.sum]
    induction z using TensorProduct.inductionOn with
    | tmul x y => rcases y with ⟨y, y'⟩; simp
    | add x y hx hy => simp [hx, hy]

theorem tensor_degenerate_left (X Y : Object R)
    (h : X.a = LinearEquiv.refl R X.carrier) :
    (X.tensor Y).a = LinearEquiv.refl R (X.tensor Y).carrier := by
  simp only [tensor, h, TensorProduct.congr_refl_refl]

theorem tensor_degenerate_right (X Y : Object R)
    (h : Y.a = LinearEquiv.refl R Y.carrier) :
    (X.tensor Y).b = LinearEquiv.refl R (X.tensor Y).carrier := by
  simp only [tensor, h, TensorProduct.congr_refl_refl]

/-- Multiplication identifies the tensor product of two rank-one objects
with the prescribed two-unit object. -/
def tensorUnitIso (a b : Rˣ) :
    CommutingAutomorphisms.Object.Iso ((unit a).tensor (unit b))
      (CommutingAutomorphisms.Object.unitPair a b) where
  linearEquiv := TensorProduct.lid R R
  commute_a z := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      change ((a : R) * x) * y = (a : R) * (x * y)
      exact mul_assoc _ _ _
    | add x y hx hy => simp [hx, hy]
  commute_b z := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      change x * ((b : R) * y) = (b : R) * (x * y)
      exact mul_left_comm _ _ _
    | add x y hx hy => simp [hx, hy]

end Object

end Module.Automorphism
