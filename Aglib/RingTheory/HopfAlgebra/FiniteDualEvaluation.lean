/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Coalgebra.DualTensorHom
public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# The canonical evaluation unit of a finite-dimensional Hopf algebra

The unit is literally the native coevaluation at one. Its inverse is literally
the image under the original antipode on the primal factor. The two inverse
laws follow from the original Hopf identities through the native tensor–Hom
equivalence. No basis is part of the construction or statement.
-/

@[expose] public section

noncomputable section

open Module WithConv
open scoped TensorProduct Module.Dual.FiniteDual

namespace HopfAlgebra

variable (k A : Type*) [Field k] [Ring A] [Algebra k A] [Coalgebra k A]
  [FiniteDimensional k A]

/-- The canonical tensor–Hom identification with convolution endomorphisms. -/
def evaluationEndEquiv : A ⊗[k] Dual k A ≃ₐ[k] WithConv (A →ₗ[k] A) :=
  (Algebra.TensorProduct.comm k A (Dual k A)).trans
    (TensorProduct.dualTensorHomAlgEquiv k A A)

@[simp]
theorem evaluationEndEquiv_ofConv (x : A ⊗[k] Dual k A) :
    (evaluationEndEquiv k A x).ofConv =
      _root_.dualTensorHom k A A (TensorProduct.comm k A (Dual k A) x) := rfl

/-- Coevaluation is the actual identity endomorphism under the canonical identification. -/
theorem evaluationEndEquiv_coevaluation :
    evaluationEndEquiv k A (coevaluation k A 1) = toConv LinearMap.id := by
  apply WithConv.ext
  exact TensorProduct.dualTensorHom_coevaluation k A

end HopfAlgebra

namespace HopfAlgebra

variable (k A : Type*) [Field k] [Ring A] [HopfAlgebra k A] [FiniteDimensional k A]

/-- Applying the antipode on the primal factor corresponds to the original antipode. -/
theorem evaluationEndEquiv_antipode_coevaluation :
    evaluationEndEquiv k A
        ((antipode k (A := A)).rTensor (Dual k A) (coevaluation k A 1)) =
      toConv (antipode k (A := A)) := by
  apply WithConv.ext
  simp only [evaluationEndEquiv_ofConv, TensorProduct.dualTensorHom_comm_rTensor,
    TensorProduct.dualTensorHom_coevaluation, LinearMap.comp_id]

/-- The actual universal evaluation unit, with the original coevaluation as its value. -/
def coevaluationUnit : (A ⊗[k] Dual k A)ˣ where
  val := coevaluation k A 1
  inv := (antipode k (A := A)).rTensor (Dual k A) (coevaluation k A 1)
  val_inv := by
    apply (evaluationEndEquiv k A).injective
    rw [map_mul (evaluationEndEquiv k A), map_one (evaluationEndEquiv k A),
      evaluationEndEquiv_coevaluation, evaluationEndEquiv_antipode_coevaluation]
    exact LinearMap.id_mul_antipode
  inv_val := by
    apply (evaluationEndEquiv k A).injective
    rw [map_mul (evaluationEndEquiv k A), map_one (evaluationEndEquiv k A),
      evaluationEndEquiv_antipode_coevaluation, evaluationEndEquiv_coevaluation]
    exact LinearMap.antipode_mul_id

@[simp]
theorem coevaluationUnit_val : (coevaluationUnit k A).val = coevaluation k A 1 := rfl

@[simp]
theorem coevaluationUnit_inv_val :
    (coevaluationUnit k A)⁻¹.val =
      (antipode k (A := A)).rTensor (Dual k A) (coevaluation k A 1) := rfl

end HopfAlgebra
