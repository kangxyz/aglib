/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Scalar extension of algebraic counit and comultiplication maps

These maps reuse the actual tensor product and its canonical tensor comparison.
No coalgebra law, field, normality, or finiteness hypothesis is added. The source
is the tensor prefix of `R5Lab.Aglib.RingTheory.IntegralClosure.FiniteEtale.Coactions`
and the two coefficient maps in `TorsorExtension` on the supplied source packet.
The original generic-fibre maps are precisely these constructions with a field
as the new base. No normalization or torsor object is imported.
-/

@[expose] public section

noncomputable section
open scoped TensorProduct
namespace Algebra.TensorProduct.BaseChange

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable {B C H : Type u} [CommRing B] [Algebra R B]
  [CommRing C] [Algebra R C] [CommRing H] [Algebra R H]

/-- Scalar extension of the actual algebra homomorphism. -/
abbrev map (f : B →ₐ[R] C) : S ⊗[R] B →ₐ[S] S ⊗[R] C :=
  Algebra.TensorProduct.map (AlgHom.id S S) f

/-- The canonical comparison between a tensor of scalar extensions and the
scalar extension of a tensor. -/
def tensorEquiv : (S ⊗[R] B) ⊗[S] (S ⊗[R] H) ≃ₐ[S] S ⊗[R] (B ⊗[R] H) :=
  (Algebra.TensorProduct.tensorTensorTensorComm R R S S S B S H).trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.lid S S)
      (AlgEquiv.refl : B ⊗[R] H ≃ₐ[R] B ⊗[R] H))

@[simp] theorem tensorEquiv_tmul (s t : S) (b : B) (h : H) :
    tensorEquiv R S ((s ⊗ₜ[R] b) ⊗ₜ[S] (t ⊗ₜ[R] h)) =
      (s * t) ⊗ₜ[R] (b ⊗ₜ[R] h) := by
  simp [tensorEquiv, Algebra.TensorProduct.lid_tmul]

@[simp] theorem tensorEquiv_symm_tmul (s : S) (b : B) (h : H) :
    (tensorEquiv R S (B := B) (H := H)).symm (s ⊗ₜ[R] (b ⊗ₜ[R] h)) =
      (s ⊗ₜ[R] b) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] h) := by
  apply (tensorEquiv R S).injective
  simp

/-- The scalar extension of the displayed algebraic counit. -/
def counit (ε : H →ₐ[R] R) : S ⊗[R] H →ₐ[S] S :=
  (Algebra.TensorProduct.rid R S S).toAlgHom.comp (map R S ε)

/-- The scalar extension of the displayed algebraic comultiplication. -/
def comul (Δ : H →ₐ[R] H ⊗[R] H) :
    S ⊗[R] H →ₐ[S] (S ⊗[R] H) ⊗[S] (S ⊗[R] H) :=
  (tensorEquiv R S).symm.toAlgHom.comp (map R S Δ)

end Algebra.TensorProduct.BaseChange
