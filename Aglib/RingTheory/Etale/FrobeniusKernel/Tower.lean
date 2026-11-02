/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.FrobeniusBaseChange.Tower
public import Aglib.RingTheory.Etale.FrobeniusKernel.BaseChange

/-! # Original-map representation through iterated base change -/

@[expose] public noncomputable section

open scoped TensorProduct
open Module

namespace Algebra.FrobeniusKernel

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
  (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
  (Φ : M →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA] M)
  (R : Type*) [CommRing R] [Algebra A R]
  {ι : Type*} [Fintype ι] (b : Basis ι R (R ⊗[A] M))
  (T : Type*) [CommRing T] [Algebra R T]
  (S : Type*) [CommRing S] [Algebra A S] [Algebra R S] [Algebra T S]
  [IsScalarTower A R S] [IsScalarTower R T S]

/-- The equation algebra of the first extension, after a second scalar extension,
represents fixed points on the original module's direct tensor extension. -/
def homIteratedBaseChangeEquivFixed :
    (T ⊗[R] CoordinateAlgebra p
      (coefficientMatrix p hp (LinearMap.primeCast_eq_zero_baseChange p hA R)
        (LinearMap.frobeniusBaseChange p hp hA Φ R) b) →ₐ[T] S) ≃
      {z : S ⊗[A] M // LinearMap.frobeniusBaseChange p hp hA Φ S z = z} :=
  (homBaseChangeEquivFixed p hp (LinearMap.primeCast_eq_zero_baseChange p hA R)
    (LinearMap.frobeniusBaseChange p hp hA Φ R) b T S).trans
      (LinearMap.frobeniusFixedCancelBaseChange p hp hA Φ R S)

variable {S} {U : Type*} [CommRing U] [Algebra A U] [Algebra R U] [Algebra T U]
  [IsScalarTower A R U] [IsScalarTower R T U]

/-- Naturality retains both the original scalar map and the original module. -/
theorem homIteratedBaseChangeEquivFixed_naturality (f : S →ₐ[T] U)
    (h : T ⊗[R] CoordinateAlgebra p
      (coefficientMatrix p hp (LinearMap.primeCast_eq_zero_baseChange p hA R)
        (LinearMap.frobeniusBaseChange p hp hA Φ R) b) →ₐ[T] S) :
    (homIteratedBaseChangeEquivFixed p hp hA Φ R b T U (f.comp h)).val =
      _root_.TensorProduct.map ((f.restrictScalars R).restrictScalars A).toLinearMap LinearMap.id
        (homIteratedBaseChangeEquivFixed p hp hA Φ R b T S h).val := by
  change _root_.TensorProduct.AlgebraTensorModule.cancelBaseChange A R U U M
      (homBaseChangeEquivFixed p hp (LinearMap.primeCast_eq_zero_baseChange p hA R)
        (LinearMap.frobeniusBaseChange p hp hA Φ R) b T U (f.comp h)).val = _
  rw [homBaseChangeEquivFixed_naturality]
  exact LinearMap.cancelBaseChange_tensor_map R (f.restrictScalars R) _

end Algebra.FrobeniusKernel
