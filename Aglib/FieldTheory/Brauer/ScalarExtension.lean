/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Azumaya.CentralSimple
public import Aglib.FieldTheory.Brauer.Split
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Flat.Basic

/-!
# Scalar extension and algebraically closed splitting of central simple algebras

Native left-right density implies that scalar extensions remain simple: every
nonzero two-sided ideal contains a nonzero scalar extracted by a basis-coordinate
projection. Wedderburn over an algebraically closed extension then supplies an
actual matrix splitting, with its square dimension. No separable splitting or
reduced norm is assumed in these statements.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace CSA

variable {K : Type*} [Field K] (A : CSA K) (L : Type*) [Field L] [Algebra K L]

private theorem baseChange_mulLeftRight_tmul (a : A) (b : Aᵐᵒᵖ) (x : L ⊗[K] A) :
    ((AlgHom.mulLeftRight K A (a ⊗ₜ[K] b)).baseChange L) x =
      (1 ⊗ₜ[K] a) * x * (1 ⊗ₜ[K] b.unop) := by
  induction x using TensorProduct.inductionOn with
  | tmul l y =>
    simp [AlgHom.mulLeftRight_apply, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy =>
    simp only [map_add, hx, hy, mul_add, add_mul]

private theorem baseChange_preserves_ideal
    (I : TwoSidedIdeal (L ⊗[K] A)) (f : Module.End K A)
    {x : L ⊗[K] A} (hx : x ∈ I) : f.baseChange L x ∈ I := by
  obtain ⟨t, rfl⟩ := IsAzumaya.mulLeftRight_surjective K A f
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [baseChange_mulLeftRight_tmul]
    exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hx)
  | add t u ht hu =>
    simpa only [map_add, LinearMap.baseChange_add, LinearMap.add_apply] using I.add_mem ht hu

/-- A scalar extension of an actual central simple algebra remains a simple ring. -/
theorem isSimpleRing_baseChange : IsSimpleRing (L ⊗[K] A) := by
  classical
  let : Nontrivial (L ⊗[K] A) :=
    ⟨⟨(1 : L) ⊗ₜ[K] (1 : A), (1 : L) ⊗ₜ[K] (0 : A), fun h =>
      one_ne_zero (Module.Flat.tensorProduct_mk_injective K A L h)⟩⟩
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  obtain ⟨x, hxI, hx : x ≠ 0⟩ :=
    SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI : ⊥ < I)
  let b := Module.finBasis K A
  let c := b.baseChange L
  obtain ⟨i, hi⟩ : ∃ i, c.coord i x ≠ 0 := by
    by_contra h
    apply hx
    apply c.forall_coord_eq_zero_iff.mp
    simpa only [not_exists, not_not] using h
  let f : Module.End K A := (b.coord i).smulRight (1 : A)
  have hf : f.baseChange L = (c.coord i).smulRight (1 : L ⊗[K] A) := by
    apply c.ext
    intro j
    by_cases hji : j = i
    · subst j
      simp [f, c, Module.Basis.coord_apply, Algebra.TensorProduct.one_def]
    · simp [f, c, Module.Basis.coord_apply, hji]
  have hy : c.coord i x • (1 : L ⊗[K] A) ∈ I := by
    have h := baseChange_preserves_ideal A L I f hxI
    rw [hf] at h
    exact h
  rw [← Algebra.algebraMap_eq_smul_one] at hy
  apply I.eq_top
  have h := I.mul_mem_left (algebraMap L (L ⊗[K] A) (c.coord i x)⁻¹) _ hy
  simpa only [← map_mul, inv_mul_cancel₀ hi, map_one] using h

/-- Algebraically closed coefficient extensions genuinely split a central simple algebra. -/
theorem exists_matrix_baseChange_of_isAlgClosed [IsAlgClosed L] :
    ∃ (n : ℕ) (_ : NeZero n),
      Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) := by
  let := isSimpleRing_baseChange A L
  exact IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed L (L ⊗[K] A)

/-- The size of an actual scalar-extension splitting squares to the original dimension. -/
theorem finrank_eq_sq_of_baseChange_matrix (n : ℕ)
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    Module.finrank K A = n ^ 2 := by
  rw [← Module.finrank_baseChange (R := L), e.toLinearEquiv.finrank_eq,
    Module.finrank_matrix]
  simp [pow_two]

end CSA
