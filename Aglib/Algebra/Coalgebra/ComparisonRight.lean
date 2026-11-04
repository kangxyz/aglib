/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Coalgebra.Comparison

/-! # Coalgebra assembly with the original right comparison -/

@[expose] public noncomputable section

open scoped TensorProduct

universe u a b l

namespace Coalgebra

/-- Multiplication pullbacks with their original associativity law. -/
structure MultiplicationDiagram (R : Type u) (A : Type a) (B : Type b) (L : Type l)
    [CommSemiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] [AddCommMonoid L] [Module R L] where
  /-- The original multiplication pullback. -/
  mul : A →ₗ[R] B
  /-- The original left multiplication pullback. -/
  left : B →ₗ[R] L
  /-- The original right multiplication pullback after reassociation. -/
  right : B →ₗ[R] L
  /-- The two iterated pullbacks coincide. -/
  assoc : left ∘ₗ mul = right ∘ₗ mul

/-- Deduce coassociativity using the original diagrams and multiplication pullbacks. -/
theorem coassocFromOriginalDiagrams
    {R : Type u} [CommSemiring R]
    {A : Type a} [AddCommMonoid A] [Module R A]
    {B : Type b} [AddCommMonoid B] [Module R B]
    {L : Type l} [AddCommMonoid L] [Module R L]
    {C : A ⊗[R] A ≃ₗ[R] B} {D : B ⊗[R] A ≃ₗ[R] L}
    {E E' : A ⊗[R] B →ₗ[R] L}
    (hcoh : D.toLinearMap ∘ₗ C.toLinearMap.rTensor A =
      E ∘ₗ C.toLinearMap.lTensor A ∘ₗ (TensorProduct.assoc R A A A).toLinearMap)
    (g : MultiplicationDiagram R A B L)
    (u : A →ₗ[R] B) (uL : B →ₗ[R] L) {uR : B →ₗ[R] L}
    (hL : uL ∘ₗ C.toLinearMap = D.toLinearMap ∘ₗ u.rTensor A)
    (hR : uR ∘ₗ C.toLinearMap = E' ∘ₗ u.lTensor A) (hE : E' = E)
    (hU : g.mul = u) (hUL : g.left = uL) (hUR : g.right = uR) :
    let delta := C.symm.toLinearMap ∘ₗ u
    (TensorProduct.assoc R A A A).toLinearMap ∘ₗ delta.rTensor A ∘ₗ delta =
      delta.lTensor A ∘ₗ delta :=
  LinearEquiv.coassoc_of_product_diagram C D E u uL uR hcoh hL
    (by rw [← hE]; exact hR) (by simpa only [hU, hUL, hUR] using g.assoc)

/-- Use the coproduct determined by the already checked coassociativity law. -/
@[instance_reducible]
def ofCoassocAndCounit
    {R : Type u} [CommSemiring R] {A : Type a} [AddCommMonoid A] [Module R A]
    {delta : A →ₗ[R] A ⊗[R] A}
    (h : (TensorProduct.assoc R A A A).toLinearMap ∘ₗ delta.rTensor A ∘ₗ delta =
      delta.lTensor A ∘ₗ delta)
    (e : A →ₗ[R] R)
    (hL : e.rTensor A ∘ₗ delta = TensorProduct.mk R R A 1)
    (hR : e.lTensor A ∘ₗ delta = (TensorProduct.mk R A R).flip 1) :
    Coalgebra R A where
  comul := delta
  counit := e
  coassoc := h
  rTensor_counit_comp_comul := hL
  lTensor_counit_comp_comul := hR

end Coalgebra
