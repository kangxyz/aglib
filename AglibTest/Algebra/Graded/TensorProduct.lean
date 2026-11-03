/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Graded.TensorProduct

/-! Actual original coordinate and pure-tensor values of the canonical regrouping. -/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum

universe u i j a b c

section Fiber
variable {R : Type u} [CommSemiring R] {ι : Type i} {κ : Type j} [DecidableEq κ]
  (A : ι → Type a) [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
  (f : ι → κ)

example (x : ⨁ i, A i) (j : κ) (i : {i : ι // f i = j}) :
    DirectSum.sigmaFiberLinearEquiv (R := R) f x j i = x i.val :=
  DirectSum.sigmaFiberLinearEquiv_apply_apply f x j i
end Fiber

section Tensor
variable {R : Type u} [CommSemiring R] (M : ℕ → Type a) (N : ℕ → Type b)
  [∀ p, AddCommMonoid (M p)] [∀ p, Module R (M p)]
  [∀ q, AddCommMonoid (N q)] [∀ q, Module R (N q)]

example (p q : ℕ) (x : M p) (y : N q) :
    DirectSum.tensorTotalEquiv (R := R) M N
        (DirectSum.lof R ℕ M p x ⊗ₜ[R] DirectSum.lof R ℕ N q y) =
      DirectSum.lof R ℕ _ (p + q) (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = p + q}
          (fun s => M s.val.1 ⊗[R] N s.val.2) ⟨(p, q), rfl⟩ (x ⊗ₜ[R] y)) :=
  DirectSum.tensorTotalEquiv_lof_tmul_lof M N p q x y

example (p q : ℕ) (x : M p) (y : N q) :
    (DirectSum.tensorTotalEquiv (R := R) M N).symm
        (DirectSum.lof R ℕ _ (p + q) (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = p + q}
          (fun s => M s.val.1 ⊗[R] N s.val.2) ⟨(p, q), rfl⟩ (x ⊗ₜ[R] y))) =
      DirectSum.lof R ℕ M p x ⊗ₜ[R] DirectSum.lof R ℕ N q y :=
  DirectSum.tensorTotalEquiv_symm_lof_tmul_lof M N p q x y

example {P : Type c} [AddCommMonoid P] [Module R P]
    (F G : ((⨁ p, M p) ⊗[R] ⨁ q, N q) →ₗ[R] P)
    (h : ∀ p q (x : M p) (y : N q),
      F (DirectSum.lof R ℕ M p x ⊗ₜ[R] DirectSum.lof R ℕ N q y) =
        G (DirectSum.lof R ℕ M p x ⊗ₜ[R] DirectSum.lof R ℕ N q y)) : F = G :=
  DirectSum.tensorDirectSum_ext M N h
example :
    (TensorProduct.map
        (DirectSum.lof R ℕ M 0 ∘ₗ DFinsupp.lapply 0) (DirectSum.lof R ℕ N 1 ∘ₗ DFinsupp.lapply 1) ∘ₗ
      (DirectSum.tensorTotalEquiv (R := R) M N).symm.toLinearMap ∘ₗ DirectSum.lof R ℕ _ 1) +
      (TensorProduct.map
        (DirectSum.lof R ℕ M 1 ∘ₗ DFinsupp.lapply 1) (DirectSum.lof R ℕ N 0 ∘ₗ DFinsupp.lapply 0) ∘ₗ
      (DirectSum.tensorTotalEquiv (R := R) M N).symm.toLinearMap ∘ₗ DirectSum.lof R ℕ _ 1) =
      (DirectSum.tensorTotalEquiv (R := R) M N).symm.toLinearMap ∘ₗ DirectSum.lof R ℕ _ 1 :=
  DirectSum.tensorTotalEquiv_symm_degreeOne M N
end Tensor

section SelectedFiber

variable {R : Type u} [CommSemiring R] {ι₁ : Type i} {ι₂ : Type j} {κ : Type c}
  [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq κ]
  (M : ι₁ → Type a) (N : ι₂ → Type b)
  [∀ p, AddCommMonoid (M p)] [∀ p, Module R (M p)]
  [∀ q, AddCommMonoid (N q)] [∀ q, Module R (N q)]

example (f : ι₁ × ι₂ → κ) (p : ι₁) (q : ι₂) (x : M p) (y : N q) :
    DirectSum.tensorFiberEquiv (R := R) M N f
        (DirectSum.lof R ι₁ M p x ⊗ₜ[R] DirectSum.lof R ι₂ N q y) =
      DirectSum.lof R κ _ (f (p, q))
        (DirectSum.lof R {pq : ι₁ × ι₂ // f pq = f (p, q)}
          (fun s => M s.val.1 ⊗[R] N s.val.2) ⟨(p, q), rfl⟩ (x ⊗ₜ[R] y)) :=
  DirectSum.tensorFiberEquiv_lof_tmul_lof M N f p q x y

example (f : ι₁ × ι₂ → κ) (p : ι₁) (q : ι₂) (x : M p) (y : N q) :
    (DirectSum.tensorFiberEquiv (R := R) M N f).symm
        (DirectSum.lof R κ _ (f (p, q))
          (DirectSum.lof R {pq : ι₁ × ι₂ // f pq = f (p, q)}
            (fun s => M s.val.1 ⊗[R] N s.val.2) ⟨(p, q), rfl⟩ (x ⊗ₜ[R] y))) =
      DirectSum.lof R ι₁ M p x ⊗ₜ[R] DirectSum.lof R ι₂ N q y :=
  DirectSum.tensorFiberEquiv_symm_lof_tmul_lof M N f p q x y

end SelectedFiber

section Comparison

variable {R : Type u} [CommSemiring R] {ι₁ : Type i} {ι₂ : Type j} {κ : Type c}
  [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq κ]
  (M : ι₁ → Type a) (N : ι₂ → Type b) (P : κ → Type c)
  [∀ p, AddCommMonoid (M p)] [∀ p, Module R (M p)]
  [∀ q, AddCommMonoid (N q)] [∀ q, Module R (N q)]
  [∀ n, AddCommMonoid (P n)] [∀ n, Module R (P n)]
  (f : ι₁ × ι₂ → κ)
  (G : ∀ n, (⨁ s : {pq : ι₁ × ι₂ // f pq = n},
    M s.val.1 ⊗[R] N s.val.2) →ₗ[R] P n)
  (hG : ∀ n, Function.Bijective (G n))

example : (DirectSum.tensorFiberComparison M N f P G hG).toLinearMap =
    DirectSum.tensorFiberMap M N f P G :=
  DirectSum.tensorFiberComparison_toLinearMap M N f P G hG

example (n : κ) (z : P n) :
    (DirectSum.tensorFiberComparison M N f P G hG).symm (DirectSum.lof R κ P n z) =
      (DirectSum.tensorFiberEquiv (R := R) M N f).symm
        (DirectSum.lof R κ _ n ((DirectSum.tensorFiberDegreeEquiv M N f P G hG n).symm z)) :=
  DirectSum.tensorFiberComparison_symm_lof M N f P G hG n z

example (L : ((⨁ p, M p) ⊗[R] ⨁ q, N q) →ₗ[R] ⨁ n, P n)
    (s : ((⨁ p, M p) ⊗[R] ⨁ q, N q) ≃ₗ[R]
      ⨁ n, ⨁ t : {pq : ι₁ × ι₂ // f pq = n}, M t.val.1 ⊗[R] N t.val.2)
    (hL : DirectSum.TensorFiberMapFactorization M N f P G L s)
    (e : ∀ p q, M p →ₗ[R] N q →ₗ[R] P (f (p, q)))
    (T : ∀ p q, M p ⊗[R] N q →ₗ[R] P (f (p, q)))
    (hs : ∀ p q (x : M p) (y : N q),
      s (DirectSum.lof R ι₁ M p x ⊗ₜ[R] DirectSum.lof R ι₂ N q y) =
        DirectSum.lof R κ _ (f (p, q))
          (DirectSum.lof R {pq : ι₁ × ι₂ // f pq = f (p, q)}
            (fun t => M t.val.1 ⊗[R] N t.val.2) ⟨(p, q), rfl⟩ (x ⊗ₜ[R] y)))
    (hG : ∀ p q (z : M p ⊗[R] N q),
      G (f (p, q)) (DirectSum.lof R {pq : ι₁ × ι₂ // f pq = f (p, q)}
        (fun t => M t.val.1 ⊗[R] N t.val.2) ⟨(p, q), rfl⟩ z) = T p q z)
    (hT : ∀ p q (x : M p) (y : N q), T p q (x ⊗ₜ[R] y) = e p q x y) :
    DirectSum.TensorFiberHomogeneousEq M N f P L e :=
  DirectSum.TensorFiberMapFactorization.homogeneous M N f P G hL e T hs hG hT

end Comparison


section ChosenOperators

variable {R : Type u} [CommSemiring R] {ι : Type i}
  {A : Type a} [AddCommMonoid A] [Module R A]
  {F : ι → Type b} [∀ i, AddCommMonoid (F i)] [∀ i, Module R (F i)]
  {P : ι → Type c} [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
  (E : A ≃ₗ[R] ⨁ i, F i) (e : ∀ i, F i ≃ₗ[R] P i)

example : DirectSum.MapFactorization
    (DirectSum.mapAfterEquiv E (fun i => (e i).toLinearMap)) E
      (fun i => (e i).toLinearMap) :=
  DirectSum.mapAfterEquiv_factorization E (fun i => (e i).toLinearMap)

example : (DirectSum.equivAfterEquiv E e).toLinearMap =
    DirectSum.mapAfterEquiv E (fun i => (e i).toLinearMap) :=
  DirectSum.equivAfterEquiv_toLinearMap E e

variable [DecidableEq ι]

example (i : ι) (z : P i) :
    (DirectSum.equivAfterEquiv E e).symm (DirectSum.lof R ι P i z) =
      E.symm (DirectSum.lof R ι F i ((e i).symm z)) :=
  DirectSum.equivAfterEquiv_symm_lof E e i z

end ChosenOperators
