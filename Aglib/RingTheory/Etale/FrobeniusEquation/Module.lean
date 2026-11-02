/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.FrobeniusKernel.Module
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Inhomogeneous Frobenius equations on the original tensor module

A temporary basis realizes the equation for an arbitrary element of the
original scalar-extended module. Its natural Hom equivalence retains the
original module, original semilinear operator, and actual scalar tensor map.
For a finite free coefficient module every such element acquires a solution
after an actual etale, spectrum-surjective algebra extension. No finite root
algebra, perfectness, invertible matrix, or nontrivial test algebra is assumed.
-/

@[expose] public noncomputable section

universe u v w

open scoped TensorProduct
open Module

namespace Algebra.FrobeniusEquation

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
  {ι : Type*} [Fintype ι] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
  (Φ : M →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA] M) (b : Basis ι A M)
  (S : Type w) [CommRing S] [Algebra A S] (y : S ⊗[A] M)
  (T : Type*) [CommRing T] [Algebra A T] [Algebra S T] [IsScalarTower A S T]

/-- Original tensor solutions and coordinate solutions agree under the actual basis. -/
def differenceFiberEquivSolutions :
    {z : T ⊗[A] M // LinearMap.frobeniusBaseChange p hp hA Φ T z - z =
      _root_.TensorProduct.map (IsScalarTower.toAlgHom A S T).toLinearMap LinearMap.id y} ≃
    Solutions p ((FrobeniusKernel.coefficientMatrix p hp hA Φ b).map (algebraMap A S))
      (fun i => (b.baseChange S).repr y i) (S := T) :=
  (b.baseChange T).equivFun.toEquiv.subtypeEquiv (fun z => by
    rw [← (b.baseChange T).repr.injective.eq_iff]
    rw [Finsupp.ext_iff]
    simp only [map_sub, Finsupp.sub_apply, FrobeniusKernel.repr_frobeniusBaseChange,
      b.baseChange_repr_tensorMap, IsScalarTower.toAlgHom_apply, Matrix.map_apply,
      ← IsScalarTower.algebraMap_apply A S T, LinearEquiv.coe_toEquiv, Basis.equivFun_apply])

/-- Hom from the literal root algebra is the inhomogeneous fiber on the original tensor module. -/
def homEquivDifferenceFiber :
    (CoordinateAlgebra p
      ((FrobeniusKernel.coefficientMatrix p hp hA Φ b).map (algebraMap A S))
      (fun i => (b.baseChange S).repr y i) →ₐ[S] T) ≃
    {z : T ⊗[A] M // LinearMap.frobeniusBaseChange p hp hA Φ T z - z =
      _root_.TensorProduct.map (IsScalarTower.toAlgHom A S T).toLinearMap LinearMap.id y} :=
  (homEquivSolutions p
    ((FrobeniusKernel.coefficientMatrix p hp hA Φ b).map (algebraMap A S))
    (fun i => (b.baseChange S).repr y i)).trans
      (differenceFiberEquivSolutions p hp hA Φ b S y T).symm

/-- The forward map evaluates the original coordinate classes. -/
theorem homEquivDifferenceFiber_repr
    (h : CoordinateAlgebra p
      ((FrobeniusKernel.coefficientMatrix p hp hA Φ b).map (algebraMap A S))
      (fun i => (b.baseChange S).repr y i) →ₐ[S] T) (i : ι) :
    (b.baseChange T).repr (homEquivDifferenceFiber p hp hA Φ b S y T h).val i =
      h (coordinate p
        ((FrobeniusKernel.coefficientMatrix p hp hA Φ b).map (algebraMap A S))
        (fun i => (b.baseChange S).repr y i) i) := by
  change (b.baseChange T).repr ((b.baseChange T).equivFun.symm
    (homEquivSolutions p
      ((FrobeniusKernel.coefficientMatrix p hp hA Φ b).map (algebraMap A S))
      (fun i => (b.baseChange S).repr y i) h).val) i = _
  rw [← Basis.equivFun_apply]
  exact congrFun ((b.baseChange T).equivFun.apply_symm_apply _) i

variable {T} {U : Type*} [CommRing U] [Algebra A U] [Algebra S U] [IsScalarTower A S U]

/-- Naturality is the actual scalar tensor map on the unchanged original module. -/
theorem homEquivDifferenceFiber_naturality (f : T →ₐ[S] U)
    (h : CoordinateAlgebra p
      ((FrobeniusKernel.coefficientMatrix p hp hA Φ b).map (algebraMap A S))
      (fun i => (b.baseChange S).repr y i) →ₐ[S] T) :
    (homEquivDifferenceFiber p hp hA Φ b S y U (f.comp h)).val =
      _root_.TensorProduct.map (f.restrictScalars A).toLinearMap LinearMap.id
        (homEquivDifferenceFiber p hp hA Φ b S y T h).val := by
  apply (b.baseChange U).repr.injective
  apply Finsupp.ext
  intro i
  rw [homEquivDifferenceFiber_repr, b.baseChange_repr_tensorMap,
    homEquivDifferenceFiber_repr]
  rfl

/-- Every original tensor section acquires an inhomogeneous solution on an actual
etale, spectrum-surjective extension. The basis is internal, and the root algebra
stays in the test ring's universe even when the original module is larger. -/
theorem exists_etale_surjective_solution [Module.Free A M] [Module.Finite A M] :
    ∃ (C : Type w) (_ : CommRing C) (_ : Algebra S C) (_ : Algebra A C)
      (_ : IsScalarTower A S C),
      Algebra.Etale S C ∧
      Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) ∧
      ∃ z : C ⊗[A] M, LinearMap.frobeniusBaseChange p hp hA Φ C z - z =
        _root_.TensorProduct.map (IsScalarTower.toAlgHom A S C).toLinearMap LinearMap.id y := by
  classical
  let b := (Module.Free.chooseBasis A M).reindex
    (Fintype.equivFin (Module.Free.ChooseBasisIndex A M))
  let B := (FrobeniusKernel.coefficientMatrix p hp hA Φ b).map (algebraMap A S)
  let rhs := fun i => (b.baseChange S).repr y i
  let C := CoordinateAlgebra p B rhs
  have hS := LinearMap.primeCast_eq_zero_baseChange p hA S
  let z := homEquivDifferenceFiber p hp hA Φ b S y C (AlgHom.id S C)
  exact ⟨C, inferInstance, inferInstance, inferInstance, inferInstance,
    etale p B rhs hS, spectrum_surjective p B rhs hp hS, z.val, z.property⟩

end Algebra.FrobeniusEquation
