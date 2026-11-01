/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.CharP.Frobenius
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Algebra.Algebra.Hom

/-!
# Scalar extension of the original Frobenius-semilinear map

The map on the actual tensor module sends `s ⊗ m` to `s^p ⊗ Φ(m)`.
The prime-cast equation, rather than exact characteristic, permits zero test
algebras. No flatness of Frobenius or of scalar extension is assumed.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace LinearMap

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
  (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)

include hA in
/-- The original prime-cast equation after any algebra scalar extension. -/
theorem primeCast_eq_zero_baseChange (S : Type*) [CommRing S] [Algebra A S] :
    (p : S) = 0 := by
  simpa only [map_natCast, map_zero] using congrArg (algebraMap A S) hA

variable (Φ : M →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA] M)
  (S : Type*) [CommRing S] [Algebra A S]

/-- The scalar power map as a semilinear map over the original base. -/
def scalarFrobenius : S →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp hA] S where
  __ := (RingHom.frobeniusOfPrimeCastEqZero p hp
    (primeCast_eq_zero_baseChange p hA S)).toAddMonoidHom
  map_smul' a s := by
    simp [Algebra.smul_def, mul_pow]

/-- Scalar extension on the original tensor module, semilinear over its actual
new scalar ring. -/
def frobeniusBaseChange :
    S ⊗[A] M →ₛₗ[RingHom.frobeniusOfPrimeCastEqZero p hp
      (primeCast_eq_zero_baseChange p hA S)] S ⊗[A] M where
  __ := (TensorProduct.map (scalarFrobenius p hp hA S) Φ).toAddHom
  map_smul' s z := by
    change (TensorProduct.map (scalarFrobenius p hp hA S) Φ) (s • z) =
      _ • (TensorProduct.map (scalarFrobenius p hp hA S) Φ) z
    induction z using TensorProduct.inductionOn with
    | tmul t m =>
      simp [TensorProduct.smul_tmul', TensorProduct.map_tmul, scalarFrobenius,
        RingHom.frobeniusOfPrimeCastEqZero_apply, smul_eq_mul, mul_pow]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

@[simp]
theorem frobeniusBaseChange_tmul (s : S) (m : M) :
    frobeniusBaseChange p hp hA Φ S (s ⊗ₜ[A] m) = (s ^ p) ⊗ₜ[A] Φ m := rfl

/-- The extension retains the original map under the original unit tensor map. -/
theorem frobeniusBaseChange_one_tmul (m : M) :
    frobeniusBaseChange p hp hA Φ S (1 ⊗ₜ[A] m) = 1 ⊗ₜ[A] Φ m := by
  simp

variable {S} {T : Type*} [CommRing T] [Algebra A T]

/-- Naturality along the actual scalar algebra map on the unchanged tensor modules. -/
theorem frobeniusBaseChange_naturality (f : S →ₐ[A] T) (z : S ⊗[A] M) :
    TensorProduct.map f.toLinearMap LinearMap.id (frobeniusBaseChange p hp hA Φ S z) =
      frobeniusBaseChange p hp hA Φ T (TensorProduct.map f.toLinearMap LinearMap.id z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end LinearMap
