/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.Lift
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Flat base change of Néron modifications

The base-changed modification is constructed by the actual divisibility universal
property. Flatness preserves the regularity needed for the inverse map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace Algebra.NeronModification

variable {B B' ι : Type*} [CommRing B] [CommRing B'] [Algebra B B']
variable [Module.Flat B B'] (p : B) (g : ι → B)

local notation "M" => Modification p g
local notation "p'" => algebraMap B B' p
local notation "g'" => (fun i => algebraMap B B' (g i))
local notation "N" => Modification p' g'
local notation "T" => B' ⊗[B] M

/-- Flat scalar extension preserves the actual regularity of the distinguished element. -/
theorem isRegular_tensor_scalar : IsRegular (algebraMap B T p) := by
  have h : IsSMulRegular M p :=
    (isSMulRegular_algebraMap_iff M).mp (isRegular_of p g).left.isSMulRegular
  have ht : IsSMulRegular T p := h.lTensor B'
  apply (Commute.isRegular_iff (Algebra.commutes p)).mpr
  exact isLeftRegular_iff.mpr ((isSMulRegular_algebraMap_iff T).mpr ht)

omit [Module.Flat B B'] in
/-- The old modification maps to the modification of the extended coefficients. -/
def baseChangeOriginal : M →ₐ[B] N := by
  let f := algebraMap B N
  have hp : IsRegular (f p) := by
    change IsRegular (algebraMap B N p)
    rw [IsScalarTower.algebraMap_apply B B' N]
    exact isRegular_of p' g'
  have hz (i : ι) : f p * coordinate p' g' i = f (g i) := by
    change algebraMap B N p * coordinate p' g' i = algebraMap B N (g i)
    rw [IsScalarTower.algebraMap_apply B B' N,
      IsScalarTower.algebraMap_apply B B' N]
    exact of_mul_coordinate p' g' i
  exact liftAlgHom p g (coordinate p' g') hz hp

omit [Module.Flat B B'] in
/-- The old coefficient map is preserved by the original comparison. -/
@[simp] theorem baseChangeOriginal_of (b : B) :
    baseChangeOriginal p g (of p g b) = of p' g' (algebraMap B B' b) := by
  change baseChangeOriginal p g (algebraMap B M b) = algebraMap B' N _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply B B' N]

omit [Module.Flat B B'] in
/-- Each old divided coordinate maps to its new divided coordinate. -/
@[simp] theorem baseChangeOriginal_coordinate (i : ι) :
    baseChangeOriginal p g (coordinate p g i) = coordinate p' g' i := by
  simp only [baseChangeOriginal, liftAlgHom_coordinate]

omit [Module.Flat B B'] in
/-- Extend the original comparison using the tensor universal property. -/
def baseChangeForward : T →ₐ[B'] N :=
  Algebra.TensorProduct.lift (Algebra.ofId B' N) (baseChangeOriginal p g)
    (fun a b => Algebra.commutes a (baseChangeOriginal p g b))

omit [Module.Flat B B'] in
/-- The forward comparison on pure tensors. -/
@[simp] theorem baseChangeForward_tmul (b : B') (m : M) :
    baseChangeForward p g (b ⊗ₜ[B] m) =
      algebraMap B' N b * baseChangeOriginal p g m := rfl

/-- The scalar inclusion sends the new distinguished element to a regular element. -/
theorem baseChangeScalar_regular : IsRegular (algebraMap B' T p') := by
  rw [← IsScalarTower.algebraMap_apply B B' T]
  exact isRegular_tensor_scalar p g

omit [Module.Flat B B'] in
/-- Pure tensors of divided coordinates satisfy the extended divisibility equations. -/
theorem baseChangeScalar_mul_coordinate (i : ι) :
    algebraMap B' T p' * ((1 : B') ⊗ₜ[B] coordinate p g i) =
      algebraMap B' T (g' i) := by
  rw [← IsScalarTower.algebraMap_apply B B' T,
    ← IsScalarTower.algebraMap_apply B B' T,
    Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply']
  change ((1 : B') ⊗ₜ[B] of p g p) * ((1 : B') ⊗ₜ[B] coordinate p g i) =
    (1 : B') ⊗ₜ[B] of p g (g i)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, of_mul_coordinate]

/-- Construct the inverse using the scalar inclusion and the actual divided pure tensors. -/
def baseChangeBackward : N →ₐ[B'] T := by
  let : CommRing T := Algebra.TensorProduct.instCommRing (R := B) (A := B') (B := M)
  let : CommSemiring T := CommRing.toCommSemiring
  let : Semiring T := CommSemiring.toSemiring
  let : Algebra B' T :=
    Algebra.TensorProduct.leftAlgebra (R := B) (S := B') (A := B') (B := M)
  exact liftAlgHom (B := B') (C := T) p' g' (fun i => (1 : B') ⊗ₜ[B] coordinate p g i)
    (baseChangeScalar_mul_coordinate p g) (baseChangeScalar_regular p g)

/-- The inverse preserves the new coefficient map. -/
@[simp] theorem baseChangeBackward_of (b : B') :
    baseChangeBackward p g (of p' g' b) = algebraMap B' T b :=
  (baseChangeBackward p g).commutes b

/-- The inverse sends a divided variable to its pure tensor. -/
@[simp] theorem baseChangeBackward_coordinate (i : ι) :
    baseChangeBackward p g (coordinate p' g' i) = (1 : B') ⊗ₜ[B] coordinate p g i := by
  simp only [baseChangeBackward, liftAlgHom_coordinate]

/-- The composite on the old modification is the canonical tensor inclusion. -/
theorem baseChangeBackward_comp_original :
    ((baseChangeBackward p g).restrictScalars B).comp (baseChangeOriginal p g) =
      (Algebra.TensorProduct.includeRight : M →ₐ[B] T) := by
  let : CommRing T := Algebra.TensorProduct.instCommRing (R := B) (A := B') (B := M)
  let : CommSemiring T := CommRing.toCommSemiring
  let : Semiring T := CommSemiring.toSemiring
  let : Algebra B T := Algebra.TensorProduct.instAlgebra (R := B) (A := B') (B := M)
  exact algHom_ext_of_isRegular (C := T) p g
    (isRegular_tensor_scalar (B' := B') p g) _ _

/-- The inverse-forward composite is the identity on the tensor algebra. -/
theorem baseChangeBackward_comp_forward :
    (baseChangeBackward p g).comp (baseChangeForward p g) = AlgHom.id B' T := by
  apply Algebra.TensorProduct.ext'
  intro b m
  change baseChangeBackward p g (baseChangeForward p g (b ⊗ₜ[B] m)) = b ⊗ₜ[B] m
  rw [baseChangeForward_tmul, map_mul, AlgHom.commutes]
  have h := DFunLike.congr_fun (baseChangeBackward_comp_original (B' := B') p g) m
  change baseChangeBackward p g (baseChangeOriginal p g m) = (1 : B') ⊗ₜ[B] m at h
  rw [h, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, mul_one, one_mul]

/-- The forward-inverse composite is the identity on the new modification. -/
theorem baseChangeForward_comp_backward :
    (baseChangeForward p g).comp (baseChangeBackward p g) = AlgHom.id B' N := by
  exact algHom_ext_of_isRegular (C := N) p' g' (isRegular_of p' g') _ _

/-- Flat base change of the actual Néron modification. -/
def baseChangeAlgEquiv : T ≃ₐ[B'] N :=
  AlgEquiv.ofAlgHom (baseChangeForward p g) (baseChangeBackward p g)
    (baseChangeForward_comp_backward p g) (baseChangeBackward_comp_forward p g)

/-- The equivalence preserves old coefficients and the new scalar factor. -/
@[simp] theorem baseChangeAlgEquiv_tmul_of (b' : B') (b : B) :
    baseChangeAlgEquiv p g (b' ⊗ₜ[B] of p g b) =
      algebraMap B' N b' * of p' g' (algebraMap B B' b) := by
  change baseChangeForward p g (b' ⊗ₜ[B] of p g b) = _
  rw [baseChangeForward_tmul, baseChangeOriginal_of]

/-- The equivalence preserves each literal divided coordinate. -/
@[simp] theorem baseChangeAlgEquiv_one_tmul_coordinate (i : ι) :
    baseChangeAlgEquiv p g ((1 : B') ⊗ₜ[B] coordinate p g i) = coordinate p' g' i := by
  change baseChangeForward p g ((1 : B') ⊗ₜ[B] coordinate p g i) = _
  rw [baseChangeForward_tmul, map_one, one_mul, baseChangeOriginal_coordinate]

end Algebra.NeronModification
