/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.Data.Sigma.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Coordinates of finite graded tensor products in a fixed total degree. -/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum

namespace TensorProduct

section Basis

variable {R P : Type*} [CommSemiring R] [DecidableEq P]
  {A B : P → Type*} [∀ p, AddCommMonoid (A p)] [∀ p, Module R (A p)]
  [∀ p, AddCommMonoid (B p)] [∀ p, Module R (B p)]
  {I : P → Type*} [∀ p, DecidableEq (I p)]
  (b : ∀ p, Module.Basis (I p) R (B p))

private def tensorSummand (p : P) : (A p ⊗[R] B p) ≃ₗ[R] ⨁ _ : I p, A p :=
  (TensorProduct.equivFinsuppOfBasisRight (b p)).trans (finsuppLEquivDirectSum R (A p) (I p))

/-- Use the original basis coordinates in each right tensor factor. -/
@[no_expose]
def tensorBasisDirectSumEquiv :
    (⨁ p, A p ⊗[R] B p) ≃ₗ[R] ⨁ t : Sigma I, A t.1 :=
  (DirectSum.congrLinearEquiv (tensorSummand b)).trans
    (DirectSum.sigmaLcurryEquiv (δ := fun (p : P) (_ : I p) => A p) R).symm

theorem tensorBasisDirectSumEquiv_apply (p : P) (i : I p) (a : A p) :
    tensorBasisDirectSumEquiv b (DirectSum.lof R P _ p (a ⊗ₜ b p i)) =
      DirectSum.lof R (Sigma I) _ ⟨p, i⟩ a := by
  unfold tensorBasisDirectSumEquiv
  let e := DirectSum.sigmaLcurryEquiv (δ := fun (p : P) (_ : I p) => A p) R
  apply e.injective
  change e (e.symm (DirectSum.congrLinearEquiv (tensorSummand b)
    (DirectSum.lof R P _ p (a ⊗ₜ b p i)))) = _
  rw [LinearEquiv.apply_symm_apply]
  rw [DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
  have h : tensorSummand b p (a ⊗ₜ b p i) = DirectSum.lof R (I p) _ i a := by
    change finsuppLEquivDirectSum R (A p) (I p)
      (TensorProduct.equivFinsuppOfBasisRight (b p) (a ⊗ₜ b p i)) = _
    rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul, Module.Basis.repr_self,
      Finsupp.mapRange_single, one_smul, finsuppLEquivDirectSum_single]
  change DirectSum.lof R P (fun p => ⨁ _ : I p, A p) p (tensorSummand b p (a ⊗ₜ b p i)) = _
  rw [h]
  change _ = DirectSum.sigmaCurry (δ := fun (p : P) (_ : I p) => A p) _
  simpa only [DirectSum.lof_eq_of] using
    (DirectSum.sigmaCurry_of (δ := fun (p : P) (_ : I p) => A p) ⟨p, i⟩ a).symm

end Basis

section Reindex

variable (rank : ℕ → ℕ) (d bound : ℕ)
  (hzero : ∀ q, bound ≤ q → rank q = 0)

private def forward :
    (Σ p : Fin (d + 1), Fin (rank (d - p.val))) →
      {j : (Σ q : Fin bound, Fin (rank q.val)) // j.1.val ≤ d} := by
  rintro ⟨p, i⟩
  let q := d - p.val
  have hq : q < bound := by
    by_contra hn
    have hz := hzero q (by omega)
    have hi := i.isLt
    dsimp [q] at hz
    omega
  exact ⟨⟨⟨q, hq⟩, i⟩, by dsimp [q]; omega⟩

private def backward :
    {j : (Σ q : Fin bound, Fin (rank q.val)) // j.1.val ≤ d} →
      (Σ p : Fin (d + 1), Fin (rank (d - p.val))) := by
  intro j
  let p : Fin (d + 1) := ⟨d - j.val.1.val, by omega⟩
  have hp : j.val.1.val = d - p.val := by
    dsimp [p]
    omega
  exact ⟨p, Fin.cast (congrArg rank hp) j.val.2⟩

/-- The antidiagonal index and the actual degree-truncated finite index
are equivalent when no rank survives beyond `bound`. -/
@[no_expose]
def antidiagonalIndexEquiv :
    (Σ p : Fin (d + 1), Fin (rank (d - p.val))) ≃
      {j : (Σ q : Fin bound, Fin (rank q.val)) // j.1.val ≤ d} where
  toFun := forward rank d bound hzero
  invFun := backward rank d bound
  left_inv := by
    intro x
    rcases x with ⟨p, i⟩
    apply Sigma.ext
    · apply Fin.ext
      dsimp [forward, backward]
      omega
    · refine (Fin.heq_ext_iff ?_).2 ?_
      · dsimp [forward, backward]
        congr 1
        omega
      · simp [forward, backward]
  right_inv := by
    intro j
    apply Subtype.ext
    apply Sigma.ext
    · apply Fin.ext
      dsimp [forward, backward]
      omega
    · refine (Fin.heq_ext_iff ?_).2 ?_
      · dsimp [forward, backward]
        congr 1
        omega
      · simp [forward, backward]

/-- The equivalence reads the degree of the original antidiagonal literally. -/
theorem antidiagonalIndexEquiv_degree (p : Fin (d + 1))
    (i : Fin (rank (d - p.val))) :
    ((antidiagonalIndexEquiv rank d bound hzero) ⟨p, i⟩).val.1.val = d - p.val := by
  unfold antidiagonalIndexEquiv forward
  rfl

/-- The original forward index retains the literal basis vector at its original grade. -/
theorem antidiagonalIndexEquiv_value (p : Fin (d + 1))
    (i : Fin (rank (d - p.val))) :
    ∃ h : d - p.val < bound,
      ((antidiagonalIndexEquiv rank d bound hzero) ⟨p, i⟩).val =
        ⟨⟨d - p.val, h⟩, i⟩ := by
  unfold antidiagonalIndexEquiv forward
  exact ⟨_, rfl⟩

end Reindex

universe ur ua ub

variable {R : Type ur} [CommRing R] (A : ℕ → Type ua)
  [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
  (d bound : ℕ) (rank : ℕ → ℕ)
  (hzero : ∀ q, bound ≤ q → rank q = 0)
  (B : Fin (d + 1) → Type ub)
  [∀ p, AddCommGroup (B p)] [∀ p, Module R (B p)]
  (basis : ∀ p, Module.Basis (Fin (rank (d - p.val))) R (B p))

private def indexLinearEquiv {i j : ℕ} (h : i = j) : A i ≃ₗ[R] A j :=
  h ▸ LinearEquiv.refl R (A i)

private theorem indexLinearEquiv_apply {i j : ℕ} (h : i = j) (a : A i) :
    indexLinearEquiv (R := R) A h a = cast (congrArg A h) a := by
  subst j
  rfl

/-- The forced equality of the original antidiagonal coordinate and its
reindexed target coordinate, as a linear equivalence. -/
def antidiagonalCoefficientLinearEquiv (p : Fin (d + 1))
    (i : Fin (rank (d - p.val))) :
    A p.val ≃ₗ[R]
      A (d - ((antidiagonalIndexEquiv rank d bound hzero) ⟨p, i⟩).val.1.val) := by
  have hp : p.val = d -
      ((antidiagonalIndexEquiv rank d bound hzero) ⟨p, i⟩).val.1.val := by
    rw [antidiagonalIndexEquiv_degree]
    omega
  exact hp ▸ LinearEquiv.refl R (A p.val)

/-- Tensor basis coordinates, finite direct sum/product, and the exact
antidiagonal reindexing to the degree-truncated original coordinates. -/
def tensorBasisAntidiagonalEquiv :
    (⨁ p : Fin (d + 1), A p.val ⊗[R] B p) ≃ₗ[R]
      (∀ j : {j : (Σ q : Fin bound, Fin (rank q.val)) // j.1.val ≤ d},
        A (d - j.val.1.val)) := by
  let I : Fin (d + 1) → Type := fun p => Fin (rank (d - p.val))
  let L := (Σ p : Fin (d + 1), I p)
  let e := antidiagonalIndexEquiv rank d bound hzero
  let h : (⨁ p : Fin (d + 1), A p.val ⊗[R] B p) ≃ₗ[R]
      (⨁ t : L, A t.1.val) :=
    tensorBasisDirectSumEquiv (A := fun p : Fin (d + 1) => A p.val)
      (B := B) (I := I) basis
  let f : (⨁ t : L, A t.1.val) ≃ₗ[R] (∀ t : L, A t.1.val) :=
    DirectSum.linearEquivFunOnFintype R L (fun t : L => A t.1.val)
  let M : {j : (Σ q : Fin bound, Fin (rank q.val)) // j.1.val ≤ d} → Type ua :=
    fun j => A (d - j.val.1.val)
  let c : (∀ t : L, A t.1.val) ≃ₗ[R] (∀ t : L, M (e t)) :=
    LinearEquiv.piCongrRight fun t : L =>
      antidiagonalCoefficientLinearEquiv (R := R) A d bound rank hzero t.1 t.2
  let g : (∀ t : L, M (e t)) ≃ₗ[R] (∀ j, M j) :=
    LinearEquiv.piCongrLeft R M e
  exact h.trans (f.trans (c.trans g))

/-- The uniquely forced coefficient cast from antidiagonal degree `p` to
the target degree `d-q`. -/
def antidiagonalCoefficient (p : Fin (d + 1))
    (i : Fin (rank (d - p.val))) (a : A p.val) :
    A (d - ((antidiagonalIndexEquiv rank d bound hzero) ⟨p, i⟩).val.1.val) :=
  antidiagonalCoefficientLinearEquiv (R := R) A d bound rank hzero p i a

/-- In the original index family the coefficient transport is the forced degree cast. -/
theorem antidiagonalCoefficient_eq_cast (p : Fin (d + 1))
    (i : Fin (rank (d - p.val))) (a : A p.val)
    (h : p.val = d - ((antidiagonalIndexEquiv rank d bound hzero) ⟨p, i⟩).val.1.val) :
    antidiagonalCoefficient (R := R) A d bound rank hzero p i a =
      cast (congrArg A h) a := by
  unfold antidiagonalCoefficient antidiagonalCoefficientLinearEquiv
  exact indexLinearEquiv_apply (R := R) A h a

/-- The composite sends the original pure tensor in the `p` summand to
one finite-product coordinate, with only the forced degree cast. -/
theorem tensorBasisAntidiagonalEquiv_lof
    [DecidableEq {j : (Σ q : Fin bound, Fin (rank q.val)) // j.1.val ≤ d}]
    (p : Fin (d + 1)) (i : Fin (rank (d - p.val))) (a : A p.val) :
    tensorBasisAntidiagonalEquiv A d bound rank hzero B basis
      (DirectSum.lof R (Fin (d + 1))
        (fun p => A p.val ⊗[R] B p) p (a ⊗ₜ basis p i)) =
      Pi.single ((antidiagonalIndexEquiv rank d bound hzero) ⟨p, i⟩)
        (antidiagonalCoefficient (R := R) A d bound rank hzero p i a) := by
  let I : Fin (d + 1) → Type := fun p => Fin (rank (d - p.val))
  let L := (Σ p : Fin (d + 1), I p)
  let e := antidiagonalIndexEquiv rank d bound hzero
  let h : (⨁ p : Fin (d + 1), A p.val ⊗[R] B p) ≃ₗ[R]
      (⨁ t : L, A t.1.val) :=
    tensorBasisDirectSumEquiv (A := fun p : Fin (d + 1) => A p.val)
      (B := B) (I := I) basis
  let f : (⨁ t : L, A t.1.val) ≃ₗ[R] (∀ t : L, A t.1.val) :=
    DirectSum.linearEquivFunOnFintype R L (fun t : L => A t.1.val)
  let M : {j : (Σ q : Fin bound, Fin (rank q.val)) // j.1.val ≤ d} → Type ua :=
    fun j => A (d - j.val.1.val)
  let c : (∀ t : L, A t.1.val) ≃ₗ[R] (∀ t : L, M (e t)) :=
    LinearEquiv.piCongrRight fun t : L =>
      antidiagonalCoefficientLinearEquiv (R := R) A d bound rank hzero t.1 t.2
  let g : (∀ t : L, M (e t)) ≃ₗ[R] (∀ j, M j) :=
    LinearEquiv.piCongrLeft R M e
  change g (c (f (h (DirectSum.lof R (Fin (d + 1))
    (fun p => A p.val ⊗[R] B p) p (a ⊗ₜ basis p i))))) = _
  rw [tensorBasisDirectSumEquiv_apply, DirectSum.linearEquivFunOnFintype_lof]
  funext j
  obtain ⟨t, rfl⟩ := e.surjective j
  change (Equiv.piCongrLeft' M e.symm).symm (c (Pi.single ⟨p, i⟩ a)) (e t) = _
  have hg : (Equiv.piCongrLeft' M e.symm).symm
      (c (Pi.single ⟨p, i⟩ a)) (e t) = c (Pi.single ⟨p, i⟩ a) t := by
    simpa only [Equiv.symm_symm] using
      Equiv.piCongrLeft'_symm_apply_apply M e.symm
        (c (Pi.single ⟨p, i⟩ a)) t
  rw [hg]
  change (antidiagonalCoefficientLinearEquiv (R := R) A d bound rank hzero t.1 t.2)
    ((Pi.single ⟨p, i⟩ a : ∀ t : L, A t.1.val) t) = _
  by_cases ht : t = (⟨p, i⟩ : L)
  · subst t
    change _ = (Pi.single (e ⟨p, i⟩)
      (antidiagonalCoefficient (R := R) A d bound rank hzero p i a) :
        ∀ j : {j : (Σ q : Fin bound, Fin (rank q.val)) // j.1.val ≤ d}, M j)
          (e ⟨p, i⟩)
    rw [Pi.single_eq_same]
    simp only [Pi.single_eq_same]
    rfl
  · have he : e ⟨p, i⟩ ≠ e t := fun h => ht (e.injective h).symm
    have hz : (Pi.single ⟨p, i⟩ a : ∀ t : L, A t.1.val) t = 0 := by
      simp [ht]
    rw [hz, map_zero]
    change 0 = (Pi.single (e ⟨p, i⟩)
      (antidiagonalCoefficient (R := R) A d bound rank hzero p i a) :
        ∀ j : {j : (Σ q : Fin bound, Fin (rank q.val)) // j.1.val ≤ d}, M j)
          (e t)
    rw [Pi.single_eq_of_ne (Ne.symm he)]

/-- A map with the original antidiagonal basis values in the target coordinates is bijective. -/
theorem bijective_of_antidiagonal_basis_values
    {T : Type*} [AddCommGroup T] [Module R T]
    [DecidableEq {j : (Σ q : Fin bound, Fin (rank q.val)) // j.1.val ≤ d}]
    (e : T ≃ₗ[R] (∀ j : {j : (Σ q : Fin bound, Fin (rank q.val)) // j.1.val ≤ d},
      A (d - j.val.1.val)))
    (f : (⨁ p : Fin (d + 1), A p.val ⊗[R] B p) →ₗ[R] T)
    (h : ∀ (p : Fin (d + 1)) (i : Fin (rank (d - p.val))) (a : A p.val),
      e (f (DirectSum.lof R (Fin (d + 1))
        (fun p => A p.val ⊗[R] B p) p (a ⊗ₜ basis p i))) =
        Pi.single ((antidiagonalIndexEquiv rank d bound hzero) ⟨p, i⟩)
          (antidiagonalCoefficient (R := R) A d bound rank hzero p i a)) :
    Function.Bijective f := by
  let E := tensorBasisAntidiagonalEquiv A d bound rank hzero B basis
  have he : e.toLinearMap.comp f = E.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.curry_injective
    apply LinearMap.ext
    intro a
    apply (basis p).ext
    intro i
    simp only [TensorProduct.curry_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact (h p i a).trans (tensorBasisAntidiagonalEquiv_lof A d bound rank hzero B basis p i a).symm
  apply (e.bijective.of_comp_iff' f).mp
  change Function.Bijective (e.toLinearMap.comp f)
  rw [he]
  exact E.bijective

end TensorProduct
