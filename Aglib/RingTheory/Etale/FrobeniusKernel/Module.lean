/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.FrobeniusBaseChange
public import Aglib.RingTheory.Etale.FrobeniusKernel
public import Aglib.LinearAlgebra.TensorProduct.Basis

/-!
# The polynomial kernel represents the original semilinear fixed points

A supplied finite basis is used only to realize the polynomial equations.
The represented points are fixed points of the original tensor-extended map;
the forward equation and naturality retain that actual map and tensor module.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Module

namespace Algebra.FrobeniusKernel

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
  {ι : Type*} [Fintype ι] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
  (Φ : M →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA] M) (b : Basis ι A M)

/-- The coefficients of the original semilinear map in a temporary basis. -/
def coefficientMatrix : Matrix ι ι A := fun i j => b.repr (Φ (b j)) i

variable (S : Type*) [CommRing S] [Algebra A S]

/-- Coordinates of the actual scalar-extended operator, not a replacement map. -/
theorem repr_frobeniusBaseChange (z : S ⊗[A] M) (i : ι) :
    (b.baseChange S).repr (LinearMap.frobeniusBaseChange p hp hA Φ S z) i =
      ∑ j, algebraMap A S (coefficientMatrix p hp hA Φ b i j) *
        ((b.baseChange S).repr z j) ^ p := by
  conv_lhs => rw [← (b.baseChange S).sum_repr z]
  simp [map_sum, map_smulₛₗ, coefficientMatrix, Algebra.smul_def, mul_comm]

/-- Fixed points and solutions coincide through the actual base-changed basis. -/
def fixedEquivSolutions :
    {z : S ⊗[A] M // LinearMap.frobeniusBaseChange p hp hA Φ S z = z} ≃
      Solutions p (coefficientMatrix p hp hA Φ b) (S := S) :=
  (b.baseChange S).equivFun.toEquiv.subtypeEquiv (fun z => by
    rw [← (b.baseChange S).repr.injective.eq_iff]
    rw [Finsupp.ext_iff]
    simp only [repr_frobeniusBaseChange, LinearEquiv.coe_toEquiv, Basis.equivFun_apply])

/-- Hom from the original equation quotient is the fixed kernel of the original
semilinear map after scalar extension. -/
def homEquivFixed :
    (CoordinateAlgebra p (coefficientMatrix p hp hA Φ b) →ₐ[A] S) ≃
      {z : S ⊗[A] M // LinearMap.frobeniusBaseChange p hp hA Φ S z = z} :=
  (homEquivSolutions p (coefficientMatrix p hp hA Φ b)).trans
    (fixedEquivSolutions p hp hA Φ b S).symm

/-- The forward comparison evaluates the literal polynomial coordinates. -/
theorem homEquivFixed_repr
    (h : CoordinateAlgebra p (coefficientMatrix p hp hA Φ b) →ₐ[A] S) (i : ι) :
    (b.baseChange S).repr (homEquivFixed p hp hA Φ b S h).val i =
      h (coordinate p (coefficientMatrix p hp hA Φ b) i) := by
  change (b.baseChange S).repr ((b.baseChange S).equivFun.symm
    (homEquivSolutions p (coefficientMatrix p hp hA Φ b) h).val) i = _
  rw [← Basis.equivFun_apply]
  exact congrFun ((b.baseChange S).equivFun.apply_symm_apply _) i

variable {S} {T : Type*} [CommRing T] [Algebra A T]

/-- Naturality of the represented fixed point is the actual scalar tensor map. -/
theorem homEquivFixed_naturality (f : S →ₐ[A] T)
    (h : CoordinateAlgebra p (coefficientMatrix p hp hA Φ b) →ₐ[A] S) :
    (homEquivFixed p hp hA Φ b T (f.comp h)).val =
      _root_.TensorProduct.map f.toLinearMap LinearMap.id (homEquivFixed p hp hA Φ b S h).val := by
  apply (b.baseChange T).repr.injective
  apply Finsupp.ext
  intro i
  rw [homEquivFixed_repr, b.baseChange_repr_tensorMap, homEquivFixed_repr]
  rfl

end Algebra.FrobeniusKernel
