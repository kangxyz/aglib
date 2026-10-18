/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.ScalarExtension
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Completion of finite algebras as an actual algebra tensor product
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace AdicCompletion

open TensorProduct

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)

/-- The actual tensor comparison, before imposing finiteness. -/
def tensorToExtendedCompletion :
    AdicCompletion I R ⊗[R] S →ₗ[R] AdicCompletion (I.map (algebraMap R S)) S :=
  (mapIdealLinearEquiv I S).toLinearMap.comp ((ofTensorProduct I S).restrictScalars R)

/-- The tensor comparison preserves products of pure tensors. -/
theorem tensorToExtendedCompletion_tmul_mul
    (r t : AdicCompletion I R) (s u : S) :
    tensorToExtendedCompletion I ((r ⊗ₜ[R] s) * (t ⊗ₜ[R] u)) =
      tensorToExtendedCompletion I (r ⊗ₜ[R] s) *
        tensorToExtendedCompletion I (t ⊗ₜ[R] u) := by
  induction r using AdicCompletion.induction_on with | _ r =>
  induction t using AdicCompletion.induction_on with | _ t =>
  ext n
  simp only [smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, val_mul]
  change mapIdealQuotientEquiv (S := S) I S n (Submodule.Quotient.mk ((r n * t n) • (s * u))) =
    mapIdealQuotientEquiv (S := S) I S n (Submodule.Quotient.mk (r n • s)) *
      mapIdealQuotientEquiv (S := S) I S n (Submodule.Quotient.mk (t n • u))
  simp only [mapIdealQuotientEquiv_mk (S := S)]
  simp [Algebra.smul_def, mul_mul_mul_comm]

/-- The actual comparison is multiplicative on arbitrary tensors. -/
theorem tensorToExtendedCompletion_mul (x y : AdicCompletion I R ⊗[R] S) :
    tensorToExtendedCompletion I (x * y) =
      tensorToExtendedCompletion I x * tensorToExtendedCompletion I y := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp [add_mul, hx, hz]
  | tmul r s =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp [mul_add, hy, hz]
    | tmul t u => exact tensorToExtendedCompletion_tmul_mul I r t s u

/-- The tensor comparison fixes the integral algebra coefficients. -/
@[simp] theorem tensorToExtendedCompletion_one_tmul (s : S) :
    tensorToExtendedCompletion I (1 ⊗ₜ[R] s) =
      algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) s := by
  change mapIdealLinearEquiv I S (ofTensorProduct I S (1 ⊗ₜ[R] s)) = _
  rw [ofTensorProduct_tmul, one_smul, mapIdealLinearEquiv_of]
  rfl

/-- The actual tensor-to-completion algebra homomorphism. -/
def tensorToExtendedCompletionAlgHom :
    AdicCompletion I R ⊗[R] S →ₐ[R] AdicCompletion (I.map (algebraMap R S)) S :=
  AlgHom.ofLinearMap (tensorToExtendedCompletion I)
    (by
      change tensorToExtendedCompletion I (1 ⊗ₜ[R] (1 : S)) = 1
      rw [tensorToExtendedCompletion_one_tmul, map_one])
    (tensorToExtendedCompletion_mul I)

/-- The canonical action of the completed base ring on the extended-ideal completion. -/
@[instance_reducible] def extendedCompletionAlgebra :
    Algebra (AdicCompletion I R) (AdicCompletion (I.map (algebraMap R S)) S) :=
  ((tensorToExtendedCompletionAlgHom (S := S) I).toRingHom.comp
    Algebra.TensorProduct.includeLeftRingHom).toAlgebra

variable [IsNoetherianRing R] [Module.Finite R S]

/-- The finite algebra tensor product is the actual completion at the extended ideal. -/
def tensorEquivExtendedCompletion :
    AdicCompletion I R ⊗[R] S ≃ₐ[R] AdicCompletion (I.map (algebraMap R S)) S :=
  AlgEquiv.ofBijective (tensorToExtendedCompletionAlgHom I)
    ((mapIdealLinearEquiv I S).bijective.comp
      (ofTensorProduct_bijective_of_finite_of_isNoetherian I S))

@[simp] theorem tensorEquivExtendedCompletion_one_tmul (s : S) :
    tensorEquivExtendedCompletion I (1 ⊗ₜ[R] s) =
      algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) s :=
  tensorToExtendedCompletion_one_tmul I s

/-- The same actual tensor comparison is linear over the completed base ring. -/
def tensorEquivExtendedCompletionBase :
    letI := extendedCompletionAlgebra (S := S) I
    AdicCompletion I R ⊗[R] S ≃ₐ[AdicCompletion I R]
      AdicCompletion (I.map (algebraMap R S)) S := by
  letI := extendedCompletionAlgebra (S := S) I
  exact AlgEquiv.ofRingEquiv (f := (tensorEquivExtendedCompletion (S := S) I).toRingEquiv)
    (fun _ ↦ rfl)

end AdicCompletion
