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

Native extraction from `lean/R5Lab/Aglib/Algebra/Module/CommutingAutomorphisms/BaseChange.lean` at
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`cd5063282c9ecd026b91a51942865156b6d1ad4703ae54d69baf04b10e135227`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
namespace Module.CommutingAutomorphisms

open _root_.TensorProduct

universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

namespace Object

variable (S) [Algebra R S]

/-- Actual extension of scalars of a projective module with commuting automorphisms. -/
noncomputable def baseChange (X : Object R) : Object S where
  carrier := S ⊗[R] X.carrier
  a := X.a.baseChange R S
  b := X.b.baseChange R S
  commute := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s x => simp [X.commute]
    | add x y hx hy => simp [hx, hy]

/-- An equivariant module isomorphism remains such after scalar extension. -/
noncomputable def Iso.baseChange {X Y : Object R} (e : Iso X Y) :
    Iso (X.baseChange S) (Y.baseChange S) where
  linearEquiv := e.linearEquiv.baseChange R S
  commute_a := by
    intro x
    have h : e.linearEquiv.toLinearMap.comp X.a.toLinearMap =
        Y.a.toLinearMap.comp e.linearEquiv.toLinearMap := LinearMap.ext e.commute_a
    have hh := congrArg (LinearMap.baseChange S) h
    simp only [LinearMap.baseChange_comp] at hh
    exact LinearMap.congr_fun hh x
  commute_b := by
    intro x
    have h : e.linearEquiv.toLinearMap.comp X.b.toLinearMap =
        Y.b.toLinearMap.comp e.linearEquiv.toLinearMap := LinearMap.ext e.commute_b
    have hh := congrArg (LinearMap.baseChange S) h
    simp only [LinearMap.baseChange_comp] at hh
    exact LinearMap.congr_fun hh x

/-- Tensor products distribute over the literal direct-sum object. -/
noncomputable def baseChangeSumIso (X Y : Object R) :
    Iso ((X.sum Y).baseChange S) ((X.baseChange S).sum (Y.baseChange S)) where
  linearEquiv := TensorProduct.prodRight R S S X.carrier Y.carrier
  commute_a := by
    intro x
    have h : (TensorProduct.prodRight R S S X.carrier Y.carrier).toLinearMap.comp
        ((X.sum Y).a.toLinearMap.baseChange S) =
        (((X.a.baseChange R S).prodCongr (Y.a.baseChange R S)).toLinearMap).comp
          (TensorProduct.prodRight R S S X.carrier Y.carrier).toLinearMap := by
      ext <;> rfl
    exact LinearMap.congr_fun h x
  commute_b := by
    intro x
    have h : (TensorProduct.prodRight R S S X.carrier Y.carrier).toLinearMap.comp
        ((X.sum Y).b.toLinearMap.baseChange S) =
        (((X.b.baseChange R S).prodCongr (Y.b.baseChange R S)).toLinearMap).comp
          (TensorProduct.prodRight R S S X.carrier Y.carrier).toLinearMap := by
      ext <;> rfl
    exact LinearMap.congr_fun h x

variable {S}

theorem baseChange_degenerate_left (X : Object R)
    (h : X.a = LinearEquiv.refl R X.carrier) :
    (X.baseChange S).a = LinearEquiv.refl S (X.baseChange S).carrier := by
  change X.a.baseChange R S = _
  rw [h]
  exact LinearEquiv.baseChange_one R S X.carrier

theorem baseChange_degenerate_right (X : Object R)
    (h : X.b = LinearEquiv.refl R X.carrier) :
    (X.baseChange S).b = LinearEquiv.refl S (X.baseChange S).carrier := by
  change X.b.baseChange R S = _
  rw [h]
  exact LinearEquiv.baseChange_one R S X.carrier

/-- The canonical unit equivalence intertwines both automorphisms. -/
noncomputable def baseChangeIdIso (X : Object R) : Iso (X.baseChange R) X where
  linearEquiv := TensorProduct.lid R X.carrier
  commute_a := by
    intro x
    have h : (TensorProduct.lid R X.carrier).toLinearMap.comp
        (X.a.toLinearMap.baseChange R) = X.a.toLinearMap.comp
          (TensorProduct.lid R X.carrier).toLinearMap := by
      ext; simp
    exact LinearMap.congr_fun h x
  commute_b := by
    intro x
    have h : (TensorProduct.lid R X.carrier).toLinearMap.comp
        (X.b.toLinearMap.baseChange R) = X.b.toLinearMap.comp
          (TensorProduct.lid R X.carrier).toLinearMap := by
      ext; simp
    exact LinearMap.congr_fun h x

variable (S T) [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Canonical associativity of actual extension of scalars, including the operators. -/
noncomputable def baseChangeCompIso (X : Object R) :
    Iso ((X.baseChange S).baseChange T) (X.baseChange T) where
  linearEquiv := TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T X.carrier
  commute_a := by
    intro x
    have h : (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T X.carrier).toLinearMap.comp
        ((X.a.toLinearMap.baseChange S).baseChange T) =
        (X.a.toLinearMap.baseChange T).comp
          (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T X.carrier).toLinearMap := by
      ext; simp
    exact LinearMap.congr_fun h x
  commute_b := by
    intro x
    have h : (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T X.carrier).toLinearMap.comp
        ((X.b.toLinearMap.baseChange S).baseChange T) =
        (X.b.toLinearMap.baseChange T).comp
          (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T X.carrier).toLinearMap := by
      ext; simp
    exact LinearMap.congr_fun h x

end Object

end Module.CommutingAutomorphisms
