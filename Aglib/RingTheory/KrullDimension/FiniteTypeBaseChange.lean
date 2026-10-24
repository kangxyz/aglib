/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field

/-! # Uniform dimension bounds after field base change

A finite polynomial presentation of an algebra bounds the dimension of every
field-valued base change by its number of generators. Consequently every
finite-type algebra has one such bound, independent of the field and its map
from the base. The base ring need not be Noetherian or finite-dimensional.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v w

namespace Algebra

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]

/-- A surjective polynomial presentation bounds the dimension after any field
base change by the number of its variables. -/
theorem ringKrullDim_tensorProduct_le_of_surjective
    {ι : Type*} [Finite ι] (φ : MvPolynomial ι R →ₐ[R] A)
    (hφ : Function.Surjective φ) (K : Type w) [Field K] [Algebra R K] :
    ringKrullDim (K ⊗[R] A) ≤ Nat.card ι := by
  let ψ : K ⊗[R] MvPolynomial ι R →ₐ[K] K ⊗[R] A :=
    TensorProduct.map (AlgHom.id K K) φ
  have hψ : Function.Surjective ψ := FiniteType.baseChangeAux_surj K hφ
  let θ : MvPolynomial ι K →ₐ[K] K ⊗[R] A :=
    ψ.comp (MvPolynomial.algebraTensorAlgEquiv R K).symm.toAlgHom
  have hθ : Function.Surjective θ :=
    hψ.comp (MvPolynomial.algebraTensorAlgEquiv R K).symm.surjective
  simpa [ringKrullDim_eq_zero_of_field] using
    ringKrullDim_le_of_surjective θ.toRingHom hθ

/-- A finite-type algebra has one finite dimension bound after every field base
change, with independent universes for the base, algebra, and field. -/
theorem FiniteType.exists_ringKrullDim_tensorProduct_le [FiniteType R A] :
    ∃ n : ℕ, ∀ (K : Type w) [Field K] [Algebra R K],
      ringKrullDim (K ⊗[R] A) ≤ n := by
  obtain ⟨n, φ, hφ⟩ := (FiniteType.iff_quotient_mvPolynomial'').mp
    (inferInstance : FiniteType R A)
  refine ⟨n, fun K _ _ => ?_⟩
  simpa using ringKrullDim_tensorProduct_le_of_surjective φ hφ K

end Algebra
