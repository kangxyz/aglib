/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.SeparableElement
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# A separable element over an infinite coefficient field

The resultant of the generic characteristic polynomial and its derivative is
nonzero: a diagonal matrix with distinct entries witnesses this. Density of the
coefficient-field grid then supplies an element over the original field. This
argument assumes an actual algebraically closed matrix splitting, not a reduced
norm or a separable splitting field.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Polynomial

namespace Algebra

private theorem resultant_self_derivative_ne_zero_iff {L : Type*} [Field L]
    (p : L[X]) (hp : p.Monic) :
    p.resultant p.derivative p.natDegree p.natDegree ≠ 0 ↔ p.Separable := by
  have hd : p.derivative.natDegree ≤ p.natDegree :=
    (Polynomial.natDegree_derivative_le p).trans (Nat.sub_le _ _)
  have he : p.resultant p.derivative p.natDegree p.natDegree =
      p.resultant p.derivative := by
    have h := Polynomial.resultant_add_right_deg p p.derivative p.natDegree
      p.derivative.natDegree (p.natDegree - p.derivative.natDegree) le_rfl
    simpa only [Nat.add_sub_of_le hd, hp.coeff_natDegree,
      one_pow, one_mul] using h
  rw [he]
  constructor
  · intro h
    by_contra hs
    exact h (Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hp.ne_zero, hs⟩)
  · intro hs
    exact Polynomial.resultant_ne_zero p p.derivative hs

private def genericMatrix {L B : Type*} [Field L] [Ring B] [Algebra L B]
    {m n : ℕ} (b : Module.Basis (Fin m) L B)
    (e : B ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) L) :=
  Matrix.of fun i j => ∑ k,
    MvPolynomial.C (Matrix.entryLinearMap L L i j (e (b k))) * MvPolynomial.X k

private theorem eval_genericMatrix {L B : Type*} [Field L] [Ring B] [Algebra L B]
    {m n : ℕ} (b : Module.Basis (Fin m) L B)
    (e : B ≃ₐ[L] Matrix (Fin n) (Fin n) L) (x : Fin m → L) :
    (genericMatrix b e).map (MvPolynomial.eval x) = e (b.equivFun.symm x) := by
  ext i j
  simp [genericMatrix, Module.Basis.equivFun_symm_apply, map_sum, Matrix.sum_apply,
    smul_eq_mul, mul_comm]

private def separabilityPolynomial {L B : Type*} [Field L] [Ring B] [Algebra L B]
    {m n : ℕ} (b : Module.Basis (Fin m) L B)
    (e : B ≃ₐ[L] Matrix (Fin n) (Fin n) L) : MvPolynomial (Fin m) L :=
  (genericMatrix b e).charpoly.resultant (genericMatrix b e).charpoly.derivative n n

private theorem eval_separabilityPolynomial_ne_zero_iff
    {L B : Type*} [Field L] [Ring B] [Algebra L B] {m n : ℕ}
    (b : Module.Basis (Fin m) L B) (e : B ≃ₐ[L] Matrix (Fin n) (Fin n) L)
    (x : Fin m → L) :
    MvPolynomial.eval x (separabilityPolynomial b e) ≠ 0 ↔
      (e (b.equivFun.symm x)).charpoly.Separable := by
  unfold separabilityPolynomial
  rw [← Polynomial.resultant_map_map, ← Polynomial.derivative_map,
    ← Matrix.charpoly_map, eval_genericMatrix]
  simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] using
    resultant_self_derivative_ne_zero_iff (e (b.equivFun.symm x)).charpoly
      (e (b.equivFun.symm x)).charpoly_monic

private theorem separabilityPolynomial_ne_zero
    {L B : Type*} [Field L] [Infinite L] [Ring B] [Algebra L B] {m n : ℕ}
    (b : Module.Basis (Fin m) L B) (e : B ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    separabilityPolynomial b e ≠ 0 := by
  let d : Fin n → L := fun i => Infinite.natEmbedding L i.val
  have hd : Function.Injective d := (Infinite.natEmbedding L).injective.comp Fin.val_injective
  have hs : (Matrix.diagonal d).charpoly.Separable := by
    rw [Matrix.charpoly_diagonal]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr hd
  have h := (eval_separabilityPolynomial_ne_zero_iff b e
    (b.equivFun (e.symm (Matrix.diagonal d)))).mpr
    (by simpa only [LinearEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply] using hs)
  intro hz
  exact h (by rw [hz, map_zero])

private theorem exists_grid_eval_ne_zero {K L : Type*} [Field K] [Infinite K]
    [Field L] [Algebra K L] {m : ℕ} (p : MvPolynomial (Fin m) L) (hp : p ≠ 0) :
    ∃ x : Fin m → K, MvPolynomial.eval (fun i => algebraMap K L (x i)) p ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hp
  apply MvPolynomial.funext_set (fun _ => Set.range (algebraMap K L))
    (fun _ => Set.infinite_range_of_injective (algebraMap K L).injective)
  intro x hx
  choose y hy using fun i => hx i (Set.mem_univ i)
  have he : x = fun i => algebraMap K L (y i) := funext fun i => (hy i).symm
  rw [he, h, map_zero]

/-- In an actual algebraically closed matrix splitting over an infinite field,
there is an original element with separable minimal polynomial of full degree. -/
theorem exists_separable_minpoly_natDegree_of_splitting
    {K L A : Type*} [Field K] [Infinite K] [Field L] [IsAlgClosed L]
    [Ring A] [Algebra K L] [Algebra K A] [FiniteDimensional K A] {n : ℕ}
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    ∃ a : A, (minpoly K a).Separable ∧ (minpoly K a).natDegree = n := by
  classical
  let b := Module.finBasis K A
  let c := b.baseChange L
  obtain ⟨x, hx⟩ := exists_grid_eval_ne_zero (K := K) (separabilityPolynomial c e)
    (separabilityPolynomial_ne_zero c e)
  have hc : c.equivFun.symm (fun i => algebraMap K L (x i)) =
      1 ⊗ₜ[K] b.equivFun.symm x := by
    change (b.baseChange L).equivFun.symm (fun i => algebraMap K L (x i)) = _
    apply (b.baseChange L).equivFun.injective
    ext i
    simp only [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply,
      Module.Basis.baseChange_repr_tmul]
    change algebraMap K L (x i) = b.equivFun (b.equivFun.symm x) i • (1 : L)
    simp only [LinearEquiv.apply_symm_apply, Algebra.algebraMap_eq_smul_one]
  have hs := (eval_separabilityPolynomial_ne_zero_iff c e _).mp hx
  rw [hc] at hs
  exact ⟨b.equivFun.symm x, separable_minpoly_and_natDegree_of_splitting e _
    (Algebra.IsIntegral.isIntegral _) hs⟩

end Algebra
