/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Coalgebra.DualAlgebra
public import Mathlib.LinearAlgebra.Coevaluation

/-!
# Tensor–Hom and convolution

The native tensor–Hom map is an algebra map to the native convolution algebra
of linear maps. For a finite projective source it is an algebra equivalence,
with exactly the original linear equivalence and inverse. The native
coevaluation maps to the identity by its contraction triangle identity.
-/

@[expose] public section

noncomputable section

open Module WithConv
open scoped TensorProduct Module.Dual.FiniteDual

namespace TensorProduct

variable (R A B : Type*) [CommRing R]
  [AddCommGroup A] [Module R A] [Coalgebra R A]
  [Ring B] [Algebra R B]

/-- The native tensor–Hom map respects convolution on pure tensors. -/
theorem dualTensorHom_mul_tmul (f g : Dual R A) (b c : B) :
    toConv (_root_.dualTensorHom R A B ((f ⊗ₜ[R] b) * (g ⊗ₜ[R] c))) =
      toConv (_root_.dualTensorHom R A B (f ⊗ₜ[R] b)) *
        toConv (_root_.dualTensorHom R A B (g ⊗ₜ[R] c)) := by
  classical
  apply WithConv.ext
  apply LinearMap.ext
  intro a
  simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.dualTensorHom_apply]
  let t := Coalgebra.Repr.arbitrary R a
  have hfg : (f * g) a = ∑ i ∈ t.index, f (t.left i) * g (t.right i) :=
    t.convMul_apply (toConv f) (toConv g)
  rw [t.convMul_apply
    (toConv (_root_.dualTensorHom R A B (f ⊗ₜ[R] b)))
    (toConv (_root_.dualTensorHom R A B (g ⊗ₜ[R] c))), hfg, Finset.sum_smul]
  simp only [_root_.dualTensorHom_apply, Algebra.smul_mul_assoc,
    Algebra.mul_smul_comm, smul_smul, mul_comm]

/-- The actual tensor–Hom map, with convolution on the target linear maps. -/
def dualTensorHomAlgHom :
    Dual R A ⊗[R] B →ₐ[R] WithConv (A →ₗ[R] B) :=
  AlgHom.ofLinearMap
    ((WithConv.linearEquiv R (A →ₗ[R] B)).symm.toLinearMap ∘ₗ
      _root_.dualTensorHom R A B)
    (by
      apply WithConv.ext
      ext a
      simp [Algebra.TensorProduct.one_def, Algebra.algebraMap_eq_smul_one])
    (fun x y => by
      induction x using TensorProduct.inductionOn with
      | add x₁ x₂ h₁ h₂ =>
        simpa only [add_mul, map_add] using congrArg₂ (· + ·) h₁ h₂
      | tmul f b =>
        induction y using TensorProduct.inductionOn with
        | add y₁ y₂ h₁ h₂ =>
          simpa only [mul_add, map_add] using congrArg₂ (· + ·) h₁ h₂
        | tmul g c => exact dualTensorHom_mul_tmul R A B f g b c)

@[simp]
theorem dualTensorHomAlgHom_tmul_apply (f : Dual R A) (b : B) (a : A) :
    dualTensorHomAlgHom R A B (f ⊗ₜ[R] b) a = f a • b := rfl

@[simp]
theorem dualTensorHomAlgHom_ofConv (x : Dual R A ⊗[R] B) :
    (dualTensorHomAlgHom R A B x).ofConv = _root_.dualTensorHom R A B x := rfl

variable [Module.Finite R A] [Module.Projective R A]

/-- The native finite-projective tensor–Hom equivalence, preserving convolution multiplication. -/
def dualTensorHomAlgEquiv :
    Dual R A ⊗[R] B ≃ₐ[R] WithConv (A →ₗ[R] B) :=
  AlgEquiv.ofLinearEquiv
    (_root_.dualTensorHomEquiv R A B ≪≫ₗ (WithConv.linearEquiv R (A →ₗ[R] B)).symm)
    (dualTensorHomAlgHom R A B).map_one
    (dualTensorHomAlgHom R A B).map_mul

@[simp]
theorem dualTensorHomAlgEquiv_toLinearEquiv :
    (dualTensorHomAlgEquiv R A B).toLinearEquiv =
      _root_.dualTensorHomEquiv R A B ≪≫ₗ (WithConv.linearEquiv R (A →ₗ[R] B)).symm := rfl

@[simp]
theorem dualTensorHomAlgEquiv_ofConv (x : Dual R A ⊗[R] B) :
    (dualTensorHomAlgEquiv R A B x).ofConv = _root_.dualTensorHom R A B x := rfl

end TensorProduct

namespace TensorProduct

variable (k V : Type*) [Field k] [AddCommGroup V] [Module k V]

/-- Flipped tensor–Hom evaluation is the native contraction on an associated tensor. -/
theorem dualTensorHom_comm_apply (x : V ⊗[k] Dual k V) (v : V) :
    _root_.dualTensorHom k V V (TensorProduct.comm k V (Dual k V) x) v =
      TensorProduct.rid k V
        ((contractLeft k V).lTensor V
          (TensorProduct.assoc k V (Dual k V) V (x ⊗ₜ[k] v))) := by
  induction x using TensorProduct.inductionOn with
  | tmul w f => simp
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, add_tmul, hx, hy]

/-- Naturality on the primal tensor factor, for the actual flipped tensor–Hom map. -/
theorem dualTensorHom_comm_rTensor (s : V →ₗ[k] V) (x : V ⊗[k] Dual k V) :
    _root_.dualTensorHom k V V
        (TensorProduct.comm k V (Dual k V) (s.rTensor (Dual k V) x)) =
      s.comp (_root_.dualTensorHom k V V (TensorProduct.comm k V (Dual k V) x)) := by
  rw [LinearMap.rTensor_def, ← TensorProduct.map_comm LinearMap.id s]
  exact LinearMap.congr_fun (_root_.dualTensorHom_comp_lTensor s)
    (TensorProduct.comm k V (Dual k V) x)

/-- The tensor–Hom map on the dual is the other native contraction. -/
theorem dualTensorHom_eval_apply (x : V ⊗[k] Dual k V) (f : Dual k V) :
    _root_.dualTensorHom k (Dual k V) (Dual k V)
        ((Module.Dual.eval k V).rTensor (Dual k V) x) f =
      TensorProduct.lid k (Dual k V)
        ((contractLeft k V).rTensor (Dual k V)
          ((TensorProduct.assoc k (Dual k V) V (Dual k V)).symm (f ⊗ₜ[k] x))) := by
  induction x using TensorProduct.inductionOn with
  | tmul v g => simp
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, tmul_add, hx, hy]

variable [FiniteDimensional k V]

/-- Native coevaluation corresponds to the identity under the native tensor–Hom equivalence. -/
theorem dualTensorHom_coevaluation :
    _root_.dualTensorHom k V V
        (TensorProduct.comm k V (Dual k V) (coevaluation k V 1)) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  rw [dualTensorHom_comm_apply]
  have h := LinearMap.congr_fun (contractLeft_assoc_coevaluation' k V) (1 ⊗ₜ[k] v)
  simpa using congrArg (TensorProduct.rid k V) h

/-- Native coevaluation gives the identity on the dual through the other contraction triangle. -/
theorem dualTensorHom_eval_coevaluation :
    _root_.dualTensorHom k (Dual k V) (Dual k V)
        ((Module.Dual.eval k V).rTensor (Dual k V) (coevaluation k V 1)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro f
  rw [dualTensorHom_eval_apply]
  have h := LinearMap.congr_fun (contractLeft_assoc_coevaluation k V) (f ⊗ₜ[k] 1)
  simpa using congrArg (TensorProduct.lid k (Dual k V)) h

/-- Applying a linear map to the primal factor of native coevaluation represents that map. -/
theorem dualTensorHom_map_coevaluation {W : Type*} [AddCommGroup W] [Module k W]
    (s : V →ₗ[k] W) :
    _root_.dualTensorHom k V W
        (TensorProduct.comm k W (Dual k V)
          (s.rTensor (Dual k V) (coevaluation k V 1))) = s := by
  rw [LinearMap.rTensor_def,
    ← TensorProduct.map_comm (LinearMap.id : Dual k V →ₗ[k] Dual k V) s]
  have h := LinearMap.congr_fun (_root_.dualTensorHom_comp_lTensor (M := V) s)
    (TensorProduct.comm k V (Dual k V) (coevaluation k V 1))
  simpa [LinearMap.lTensor_def, dualTensorHom_coevaluation] using h

/-- Swapping native coevaluation agrees with native bidual evaluation on the primal factor. -/
theorem coevaluation_flip :
    (Module.Dual.eval k V).rTensor (Dual k V) (coevaluation k V 1) =
      TensorProduct.comm k (Dual k V) (Dual k (Dual k V)) (coevaluation k (Dual k V) 1) := by
  apply (_root_.dualTensorHomEquiv k (Dual k V) (Dual k V)).injective
  change _root_.dualTensorHom k (Dual k V) (Dual k V)
      ((Module.Dual.eval k V).rTensor (Dual k V) (coevaluation k V 1)) =
    _root_.dualTensorHom k (Dual k V) (Dual k V)
      (TensorProduct.comm k (Dual k V) (Dual k (Dual k V)) (coevaluation k (Dual k V) 1))
  rw [dualTensorHom_eval_coevaluation, dualTensorHom_coevaluation]

end TensorProduct
