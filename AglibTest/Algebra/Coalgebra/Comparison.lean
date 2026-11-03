/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Coalgebra.Comparison

/-! The constructor supplies the actual native coalgebra laws and original operator values. -/

@[expose] public noncomputable section
open scoped TensorProduct
universe u a b l

variable {R : Type u} [CommSemiring R]
    {A : Type a} [AddCommMonoid A] [Module R A]
    {B : Type b} [AddCommMonoid B] [Module R B]
    {L : Type l} [AddCommMonoid L] [Module R L]
    (C : A ⊗[R] A ≃ₗ[R] B) (D : B ⊗[R] A ≃ₗ[R] L)
    (E : A ⊗[R] B →ₗ[R] L) (u : A →ₗ[R] B)
    (uL uR : B →ₗ[R] L) (e : A →ₗ[R] R) (pointL pointR : B →ₗ[R] A)
    (hcoh : D.toLinearMap ∘ₗ C.toLinearMap.rTensor A =
      E ∘ₗ C.toLinearMap.lTensor A ∘ₗ (TensorProduct.assoc R A A A).toLinearMap)
    (hL : uL ∘ₗ C.toLinearMap = D.toLinearMap ∘ₗ u.rTensor A)
    (hR : uR ∘ₗ C.toLinearMap = E ∘ₗ u.lTensor A)
    (hu : uL ∘ₗ u = uR ∘ₗ u)
    (hpointL : pointL ∘ₗ C.toLinearMap =
      (TensorProduct.lid R A).toLinearMap ∘ₗ e.rTensor A)
    (hpointR : pointR ∘ₗ C.toLinearMap =
      (TensorProduct.rid R A).toLinearMap ∘ₗ e.lTensor A)
    (hunitL : pointL ∘ₗ u = LinearMap.id)
    (hunitR : pointR ∘ₗ u = LinearMap.id)


example :
    (Coalgebra.ofTensorComparison C D E u uL uR e pointL pointR
      hcoh hL hR hu hpointL hpointR hunitL hunitR).comul = C.symm.toLinearMap ∘ₗ u :=
  Coalgebra.ofTensorComparison_comul C D E u uL uR e pointL pointR
    hcoh hL hR hu hpointL hpointR hunitL hunitR

example :
    letI := Coalgebra.ofTensorComparison C D E u uL uR e pointL pointR
      hcoh hL hR hu hpointL hpointR hunitL hunitR
    TensorProduct.assoc R A A A ∘ₗ (Coalgebra.comul (R := R)).rTensor A ∘ₗ
        Coalgebra.comul = (Coalgebra.comul (R := R)).lTensor A ∘ₗ Coalgebra.comul := by
  letI := Coalgebra.ofTensorComparison C D E u uL uR e pointL pointR
    hcoh hL hR hu hpointL hpointR hunitL hunitR
  exact Coalgebra.coassoc


section AlgebraComparison

variable {A₀ : Type a} [Semiring A₀] [Algebra R A₀]
  {B₀ : Type b} [Semiring B₀] [Algebra R B₀]
  {S : Type l} [Semiring S] [Algebra R S]
  (C₀ : A₀ ⊗[R] A₀ ≃ₗ[R] B₀) (t : A₀ ⊗[R] A₀ ≃ₗ[R] S) (Φ : S →ₐ[R] B₀)
  (hF : Φ.toLinearMap ∘ₗ t.toLinearMap = C₀.toLinearMap) (u₀ : A₀ →ₐ[R] B₀)

example (ht : t ((1 : A₀) ⊗ₜ[R] (1 : A₀)) = 1) :
    C₀.symm (u₀ 1) = (1 : A₀) ⊗ₜ[R] (1 : A₀) :=
  LinearEquiv.inverse_one_of_algebra_comparison C₀ t Φ hF u₀ ht

example (a b : A₀) :
    t (C₀.symm (u₀ (a * b))) = t (C₀.symm (u₀ a)) * t (C₀.symm (u₀ b)) :=
  LinearEquiv.inverse_mul_of_algebra_comparison C₀ t Φ hF u₀ a b

end AlgebraComparison
