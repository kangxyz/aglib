/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.CrossedProduct.Primitive
public import Aglib.FieldTheory.Brauer.C1Splitting
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Constructed multiplicative cocycle primitives over infinite C₁ fields

The normalized cocycle supplies an actual central simple matrix subalgebra.
C₁ splits that algebra. Restriction of its matrix representation to the diagonal
extension field has dimension one, so the translation coefficients give a
primitive in the original native multiplicative coboundary convention.
-/

@[expose] public noncomputable section

namespace groupCohomology.CrossedProduct

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

section Representation

variable [Fintype (L ≃ₐ[K] L)] [DecidableEq (L ≃ₐ[K] L)]
variable {c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}

/-- A representation of extension-field degree canonically becomes a
one-dimensional extension-field representation. -/
theorem isMulCoboundary₂_of_representation_dimension
    [FiniteDimensional K L] (hc : IsMulCocycle₂ c) (h₁ : c (1, 1) = 1)
    (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : algebra hc h₁ →ₐ[K] Module.End K V)
    (hdim : Module.finrank K V = Module.finrank K L) : IsMulCoboundary₂ c := by
  let j : L →ₐ[K] Module.End K V := f.comp (diagonalEmbedding hc h₁)
  let : Module L V := Module.compHom V j.toRingHom
  let : IsScalarTower K L V := ⟨fun k a v => by
    change j (k • a) v = k • j a v
    rw [map_smul]
    rfl⟩
  let : FiniteDimensional L V := Module.Finite.of_restrictScalars_finite K L V
  have hV : Module.finrank L V = 1 := by
    have h := (Module.finrank_mul_finrank K L V).trans hdim
    apply Nat.mul_left_cancel (Module.finrank_pos (R := K) (M := L))
    simpa only [mul_one] using h
  apply isMulCoboundary₂_of_oneDimensional_action hc h₁ V hV f.toRingHom
  intros
  rfl

end Representation

/-- A normalized finite-Galois multiplicative two-cocycle over an infinite C₁
field is a native multiplicative coboundary, by the actual crossed-product construction. -/
theorem isMulCoboundary₂_of_isC1 [Infinite K] [FiniteDimensional K L] [IsGalois K L]
    (hK : Field.IsC1 K) {c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
    (hc : IsMulCocycle₂ c) (h₁ : c (1, 1) = 1) : IsMulCoboundary₂ c := by
  classical
  let := Fintype.ofFinite (L ≃ₐ[K] L)
  let := isSimpleRing hc h₁
  let := isCentral hc h₁
  let A : CSA K := { toAlgCat := AlgCat.of K (algebra hc h₁) }
  obtain ⟨n, hn, ⟨e⟩⟩ := CSA.exists_matrix_of_isC1 hK A
  have hcard : Fintype.card (L ≃ₐ[K] L) = Module.finrank K L := by
    rw [← Nat.card_eq_fintype_card]
    exact IsGalois.card_aut_eq_finrank K L
  have hnrank : n = Module.finrank K L := by
    have hd := e.toLinearEquiv.finrank_eq
    change Module.finrank K (algebra hc h₁) = Module.finrank K (Matrix (Fin n) (Fin n) K) at hd
    rw [finrank_algebra hc h₁, hcard, Module.finrank_matrix] at hd
    simp only [Fintype.card_fin, Module.finrank_self, mul_one] at hd
    nlinarith
  let f : algebra hc h₁ →ₐ[K] Module.End K (Fin n → K) :=
    Matrix.toLinAlgEquiv'.toAlgHom.comp e.toAlgHom
  apply isMulCoboundary₂_of_representation_dimension hc h₁ (Fin n → K) f
  simpa only [Module.finrank_pi, Fintype.card_fin] using hnrank

end groupCohomology.CrossedProduct
