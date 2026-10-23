/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.GaloisSplittingNorm
public import Aglib.FieldTheory.Tsen.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# The C₁ division-algebra argument from an actual finite Galois splitting

The determinant polynomial is constructed and descended, not supplied as an
anisotropic-form premise. Its degree is the matrix size and its number of
variables is the square of that size. Thus a division algebra with a specified
finite Galois matrix splitting over an infinite splitting field is the scalar
field. Existence of that splitting is still a separate necessary theorem.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra

variable {K L A : Type*} [Field K] [Field L] [Algebra K L]
  [Ring A] [Algebra K A] {m n : ℕ}

private theorem baseChange_coordinates (b : Module.Basis (Fin m) K A) (x : Fin m → K) :
    (b.baseChange L).equivFun.symm (algebraMap K L ∘ x) =
      (1 : L) ⊗ₜ[K] b.equivFun.symm x := by
  apply (b.baseChange L).equivFun.injective
  ext i
  simp only [LinearEquiv.apply_symm_apply, Function.comp_apply,
    Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul]
  change algebraMap K L (x i) = b.equivFun (b.equivFun.symm x) i • (1 : L)
  simp only [LinearEquiv.apply_symm_apply, Algebra.algebraMap_eq_smul_one]

/-- Vanishing of a descended actual determinant polynomial gives a nonzero
nonunit in the original algebra, not merely in its scalar extension. -/
theorem exists_nonzero_nonunit_of_descended_norm_zero
    (b : Module.Basis (Fin m) K A)
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)
    (p : MvPolynomial (Fin m) K)
    (hp : MvPolynomial.map (algebraMap K L) p =
      matrixNormPolynomial (b.baseChange L) e.toAlgHom)
    (x : Fin m → K) (hx : x ≠ 0) (hz : MvPolynomial.eval x p = 0) :
    ∃ a : A, a ≠ 0 ∧ ¬ IsUnit a := by
  refine ⟨b.equivFun.symm x, ?_, ?_⟩
  · intro h
    apply hx
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg b.equivFun h
  · intro hu
    have hzero : MvPolynomial.eval (algebraMap K L ∘ x)
        (matrixNormPolynomial (b.baseChange L) e.toAlgHom) = 0 := by
      rw [← hp, MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp, hz, map_zero]
    rw [eval_matrixNormPolynomial, baseChange_coordinates] at hzero
    have hunit : IsUnit ((1 : L) ⊗ₜ[K] b.equivFun.symm x) :=
      hu.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (hunit.map e)).ne_zero hzero

variable {D : Type*} [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Infinite L] [FiniteDimensional K L] [IsGalois K L]

/-- The actual C₁ degree-versus-dimension argument for a division algebra
admitting a specified finite Galois splitting. No reduced norm is assumed. -/
theorem finrank_eq_one_of_isC1_of_galois_splitting (hK : Field.IsC1 K)
    (n : ℕ) [NeZero n] (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    Module.finrank K D = 1 := by
  let b := Module.finBasis K D
  have hdim : Module.finrank K D = n ^ 2 := by
    calc
      Module.finrank K D = Module.finrank L (L ⊗[K] D) := by
        rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis (b.baseChange L)]
      _ = Module.finrank L (Matrix (Fin n) (Fin n) L) := e.toLinearEquiv.finrank_eq
      _ = n ^ 2 := by rw [Module.finrank_matrix]; simp [pow_two]
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn1 : n = 1 := by
    by_contra hne
    have hlarge : 1 < n := by omega
    have hlt : n < Module.finrank K D := by
      rw [hdim, pow_two]
      exact lt_mul_of_one_lt_right hn hlarge
    obtain ⟨p, hp, hhom, _⟩ := exists_normPolynomial_of_galois_splitting b e
    obtain ⟨x, hx, hz⟩ := hK _ n p hn hlt hhom
    obtain ⟨a, ha, hunit⟩ := exists_nonzero_nonunit_of_descended_norm_zero b e p hp x hx hz
    exact hunit (isUnit_iff_ne_zero.mpr ha)
  simpa [hn1] using hdim

/-- Under the same explicit splitting hypothesis, the original division algebra
is actually isomorphic to the scalar field. -/
theorem nonempty_algEquiv_of_isC1_of_galois_splitting (hK : Field.IsC1 K)
    (n : ℕ) [NeZero n] (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    Nonempty (K ≃ₐ[K] D) :=
  Module.nonempty_algEquiv_iff_finrank_eq_one.mpr
    (finrank_eq_one_of_isC1_of_galois_splitting hK n e)

end Algebra
