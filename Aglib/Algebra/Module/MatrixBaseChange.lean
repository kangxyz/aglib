/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.MatrixPresentation
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Original matrix presentations under scalar extension

The existing finite-Pi tensor isomorphism intertwines actual scalar extension with the
coefficientwise original matrix map. The original inclusion/retraction splitting and its
idempotent matrix are preserved. No flatness assumption or replacement tensor iso is used.
-/

/-!
Source: `quillen-k-theory/Quillen/Aglib/Algebra/Module/MatrixBaseChange.lean` from the supplied
frozen Quillen snapshot.
SHA-256: `5612537fc2bd18539cb6e7fa7b13a12fd9289d533411e193fb0202b522ea8bc7`.
Only native objects, maps and mathematical namespaces are used in this extraction.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct Matrix
universe u v w
namespace TensorProduct
variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {m n : ℕ}

/-- The standard finite-Pi tensor isomorphism retains the actual coefficient-ring map. -/
theorem piScalarRight_tmul_apply (a : S) (x : Fin n → R) (j : Fin n) :
    (TensorProduct.piScalarRight R S S _) (a ⊗ₜ[R] x) j = algebraMap R S (x j) * a := by
  simp [Algebra.smul_def]

/-- The standard finite-Pi tensor isomorphism transports scalar extension to the mapped
original matrix. -/
theorem piScalarRight_toMatrix (f : (Fin n → R) →ₗ[R] (Fin m → R))
    (z : S ⊗[R] (Fin n → R)) :
    (TensorProduct.piScalarRight R S S _) (f.baseChange S z) =
      (LinearMap.toMatrix' f).map (algebraMap R S) *ᵥ (TensorProduct.piScalarRight R S S _) z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Matrix.mulVec_add, hx, hy]
  | tmul a x =>
    funext j
    rw [LinearMap.baseChange_tmul, piScalarRight_tmul_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, piScalarRight_tmul_apply]
    simp only [← mul_assoc]
    rw [← Finset.sum_mul]
    congr 1
    have h := congrArg (fun y : Fin m → R => algebraMap R S (y j))
      (LinearMap.toMatrix'_mulVec f x)
    simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul] using h.symm

end TensorProduct

namespace Module.Projective
variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M] {n : ℕ}
variable (i : M →ₗ[R] Fin n → R) (r : (Fin n → R) →ₗ[R] M)

/-- The original inclusion after scalar extension and the standard finite-Pi comparison. -/
def baseChangeInclusion : (S ⊗[R] M) →ₗ[S] (Fin n → S) :=
  ((TensorProduct.piScalarRight R S S (Fin n))).toLinearMap.comp (i.baseChange S)

/-- The original retraction after the inverse standard finite-Pi comparison. -/
def baseChangeRetraction : (Fin n → S) →ₗ[S] (S ⊗[R] M) :=
  (r.baseChange S).comp ((TensorProduct.piScalarRight R S S (Fin n))).symm.toLinearMap

/-- The actual scalar-extended inclusion and retraction preserve the original splitting. -/
theorem baseChange_split (h : r.comp i = LinearMap.id) :
    (baseChangeRetraction S r).comp (baseChangeInclusion S i) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change r.baseChange S ((TensorProduct.piScalarRight R S S (Fin n)).symm
    (TensorProduct.piScalarRight R S S (Fin n) (i.baseChange S x))) = x
  rw [LinearEquiv.symm_apply_apply]
  have he := congrArg (fun f : M →ₗ[R] M => f.baseChange S) h
  simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_id, LinearMap.comp_apply,
    LinearMap.id_apply] using LinearMap.congr_fun he x

/-- The original scalar-extended retract matrix is exactly the coefficientwise mapped matrix. -/
theorem baseChange_retractMatrix :
    retractMatrix (baseChangeInclusion S i) (baseChangeRetraction S r) =
      (retractMatrix i r).map (algebraMap R S) := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (retractMatrix (baseChangeInclusion S i) (baseChangeRetraction S r)).mulVecLin x = _
  rw [retractMatrix_apply]
  change TensorProduct.piScalarRight R S S (Fin n)
    (i.baseChange S (r.baseChange S ((TensorProduct.piScalarRight R S S (Fin n)).symm x))) =
    (retractMatrix i r).map (algebraMap R S) *ᵥ x
  have he := TensorProduct.piScalarRight_toMatrix S (i.comp r)
    ((TensorProduct.piScalarRight R S S (Fin n)).symm x)
  simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply,
    LinearEquiv.apply_symm_apply, retractMatrix] using he

end Module.Projective
