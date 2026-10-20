/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.Automorphism.Basic
public import Aglib.Algebra.Module.CommutingAutomorphisms.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/Algebra/Module/Automorphism/BaseChange.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`de03824b96dbac9b75c784ce00eb9ccd412e7975261021c9ed429886d66334fc`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
namespace Module.Automorphism

open _root_.TensorProduct

universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

namespace Object

variable (S) [Algebra R S]

/-- Actual extension of scalars of a projective module with an automorphism. -/
noncomputable def baseChange (X : Object R) : Object S where
  carrier := S ⊗[R] X.carrier
  a := X.a.baseChange R S

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

variable {S}

theorem baseChange_degenerate (X : Object R)
    (h : X.a = LinearEquiv.refl R X.carrier) :
    (X.baseChange S).a = LinearEquiv.refl S (X.baseChange S).carrier := by
  change X.a.baseChange R S = _
  rw [h]
  exact LinearEquiv.baseChange_one R S X.carrier

/-- The canonical unit equivalence intertwines the automorphism. -/
noncomputable def baseChangeIdIso (X : Object R) : Iso (X.baseChange R) X where
  linearEquiv := TensorProduct.lid R X.carrier
  commute_a := by
    intro x
    have h : (TensorProduct.lid R X.carrier).toLinearMap.comp
        (X.a.toLinearMap.baseChange R) = X.a.toLinearMap.comp
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

section TensorCompatibility

/-- The canonical base-change equivalence respects the two tensor operators. -/
noncomputable def baseChangeTensorIso (X Y : Object R) :
    CommutingAutomorphisms.Object.Iso ((X.tensor Y).baseChange S)
      ((X.baseChange S).tensor (Y.baseChange S)) where
  linearEquiv := TensorProduct.AlgebraTensorModule.distribBaseChange R S X.carrier Y.carrier
  commute_a := by
    intro z
    have h :
        (TensorProduct.AlgebraTensorModule.distribBaseChange R S X.carrier
          Y.carrier).toLinearMap.comp
          ((TensorProduct.congr X.a (LinearEquiv.refl R Y.carrier)).toLinearMap.baseChange S) =
        (TensorProduct.congr (X.a.baseChange R S)
          (LinearEquiv.refl S (S ⊗[R] Y.carrier))).toLinearMap.comp
          (TensorProduct.AlgebraTensorModule.distribBaseChange R S X.carrier
            Y.carrier).toLinearMap := by
      ext
      simp
    exact LinearMap.congr_fun h z
  commute_b := by
    intro z
    have h :
        (TensorProduct.AlgebraTensorModule.distribBaseChange R S X.carrier
          Y.carrier).toLinearMap.comp
          ((TensorProduct.congr (LinearEquiv.refl R X.carrier) Y.a).toLinearMap.baseChange S) =
        (TensorProduct.congr (LinearEquiv.refl S (S ⊗[R] X.carrier))
          (Y.a.baseChange R S)).toLinearMap.comp
          (TensorProduct.AlgebraTensorModule.distribBaseChange R S X.carrier
            Y.carrier).toLinearMap := by
      ext
      simp
    exact LinearMap.congr_fun h z

/-- Extension of scalars carries a unit operator to its image unit operator. -/
noncomputable def baseChangeUnitIso (a : Rˣ) :
    Iso ((unit a).baseChange S) (unit (Units.map (algebraMap R S).toMonoidHom a)) where
  linearEquiv := TensorProduct.AlgebraTensorModule.rid R S S
  commute_a := by
    intro z
    have h : (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp
        ((LinearEquiv.smulOfUnit a : R ≃ₗ[R] R).toLinearMap.baseChange S) =
        (LinearEquiv.smulOfUnit (Units.map (algebraMap R S).toMonoidHom a) :
          S ≃ₗ[S] S).toLinearMap.comp
          (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro s r
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
        LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.rid_tmul]
      change ((a : R) * r) • s = (algebraMap R S (a : R)) * (r • s)
      simp only [Algebra.smul_def, map_mul, mul_assoc]
    exact LinearMap.congr_fun h z

end TensorCompatibility

end Object

end Module.Automorphism
