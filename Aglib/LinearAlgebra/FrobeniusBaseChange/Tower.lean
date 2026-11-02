/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.FrobeniusBaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The original Frobenius map through iterated scalar extension

The native tensor cancellation equivalence intertwines the iterated and direct
Frobenius-semilinear scalar extensions. In particular a localization followed by
another scalar extension retains the original operator, not just its matrix.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace LinearMap

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
  (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
  (Φ : M →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA] M)
  (R : Type*) [CommRing R] [Algebra A R]
  (S : Type*) [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower A R S]

/-- The full Frobenius square for the native cancellation of iterated base change. -/
theorem frobeniusBaseChange_cancelBaseChange (z : S ⊗[R] (R ⊗[A] M)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S M
      (frobeniusBaseChange p hp (primeCast_eq_zero_baseChange p hA R)
        (frobeniusBaseChange p hp hA Φ R) S z) =
      frobeniusBaseChange p hp hA Φ S
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S M z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s z =>
    induction z using TensorProduct.inductionOn with
    | tmul r m => simp [Algebra.smul_def, mul_pow]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The same original fixed kernel after cancelling an iterated scalar extension. -/
def frobeniusFixedCancelBaseChange :
    {z : S ⊗[R] (R ⊗[A] M) //
      frobeniusBaseChange p hp (primeCast_eq_zero_baseChange p hA R)
        (frobeniusBaseChange p hp hA Φ R) S z = z} ≃
      {z : S ⊗[A] M // frobeniusBaseChange p hp hA Φ S z = z} :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S M).toEquiv.subtypeEquiv
    (fun z => by
      rw [← (TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S M).injective.eq_iff,
        frobeniusBaseChange_cancelBaseChange]
      rfl)

@[simp]
theorem frobeniusFixedCancelBaseChange_apply
    (z : {z : S ⊗[R] (R ⊗[A] M) //
      frobeniusBaseChange p hp (primeCast_eq_zero_baseChange p hA R)
        (frobeniusBaseChange p hp hA Φ R) S z = z}) :
    (frobeniusFixedCancelBaseChange p hp hA Φ R S z).val =
      TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S M z.val := rfl

variable {S} {T : Type*} [CommRing T] [Algebra A T] [Algebra R T] [IsScalarTower A R T]

/-- Native cancellation commutes with the actual scalar tensor maps. -/
theorem cancelBaseChange_tensor_map (f : S →ₐ[R] T) (z : S ⊗[R] (R ⊗[A] M)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange A R T T M
      (TensorProduct.map f.toLinearMap LinearMap.id z) =
      TensorProduct.map (f.restrictScalars A).toLinearMap LinearMap.id
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S M z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s z =>
    induction z using TensorProduct.inductionOn with
    | tmul r m => simp [Algebra.smul_def]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

end LinearMap
