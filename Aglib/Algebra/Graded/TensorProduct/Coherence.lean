/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Graded.TensorProduct

/-!
# Whole associativity from original graded tensor values

Four given total tensor maps, their original homogeneous values, and a
degree-preserving associator map determine the whole tensor diagram. The
component associativity equation is proved before any geometric realization.
-/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum

universe u m n o p q s t

namespace DirectSum

variable {R : Type u} [CommSemiring R]
  (M : ℕ → Type m) (N : ℕ → Type n) (O : ℕ → Type o)
  (P : ℕ → Type p) (Q : ℕ → Type q) (S : ℕ → Type s) (T : ℕ → Type t)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommMonoid (O i)] [∀ i, Module R (O i)]
  [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
  [∀ i, AddCommMonoid (Q i)] [∀ i, Module R (Q i)]
  [∀ i, AddCommMonoid (S i)] [∀ i, Module R (S i)]
  [∀ i, AddCommMonoid (T i)] [∀ i, Module R (T i)]

/-- Whole associativity of supplied total maps follows from their original
homogeneous values and the actual degreewise associator equation. -/
theorem tensorTotalMap_assoc_of_values
    (L_MN : ((⨁ i, M i) ⊗[R] ⨁ j, N j) →ₗ[R] ⨁ d, P d)
    (L_PO : ((⨁ d, P d) ⊗[R] ⨁ r, O r) →ₗ[R] ⨁ n, T n)
    (L_NO : ((⨁ j, N j) ⊗[R] ⨁ r, O r) →ₗ[R] ⨁ d, Q d)
    (L_MQ : ((⨁ i, M i) ⊗[R] ⨁ d, Q d) →ₗ[R] ⨁ n, S n)
    (a : (⨁ n, S n) →ₗ[R] ⨁ n, T n)
    (F_MN : ∀ i j d, i + j = d → M i → N j → P d)
    (F_PO : ∀ d r n, d + r = n → P d → O r → T n)
    (F_NO : ∀ j r d, j + r = d → N j → O r → Q d)
    (F_MQ : ∀ i d n, i + d = n → M i → Q d → S n)
    (a_n : ∀ n, S n →ₗ[R] T n)
    (hMN : ∀ i j d (h : i + j = d) (x : M i) (y : N j),
      L_MN (lof R ℕ M i x ⊗ₜ[R] lof R ℕ N j y) =
        lof R ℕ P d (F_MN i j d h x y))
    (hPO : ∀ d r n (h : d + r = n) (x : P d) (z : O r),
      L_PO (lof R ℕ P d x ⊗ₜ[R] lof R ℕ O r z) =
        lof R ℕ T n (F_PO d r n h x z))
    (hNO : ∀ j r d (h : j + r = d) (y : N j) (z : O r),
      L_NO (lof R ℕ N j y ⊗ₜ[R] lof R ℕ O r z) =
        lof R ℕ Q d (F_NO j r d h y z))
    (hMQ : ∀ i d n (h : i + d = n) (x : M i) (y : Q d),
      L_MQ (lof R ℕ M i x ⊗ₜ[R] lof R ℕ Q d y) =
        lof R ℕ S n (F_MQ i d n h x y))
    (ha : ∀ n (x : S n), a (lof R ℕ S n x) = lof R ℕ T n (a_n n x))
    (hassoc : ∀ i j r (x : M i) (y : N j) (z : O r),
      F_PO (i + j) r (i + j + r) rfl (F_MN i j (i + j) rfl x y) z =
        a_n (i + j + r)
          (F_MQ i (j + r) (i + j + r) (Nat.add_assoc i j r).symm x
            (F_NO j r (j + r) rfl y z))) :
    L_PO ∘ₗ L_MN.rTensor (⨁ r, O r) =
      a ∘ₗ L_MQ ∘ₗ L_NO.lTensor (⨁ i, M i) ∘ₗ
        (TensorProduct.assoc R (⨁ i, M i) (⨁ j, N j) (⨁ r, O r)).toLinearMap := by
  apply TensorProduct.ext
  apply tensorDirectSum_ext (R := R) M N
  intro i j x y
  apply DirectSum.linearMap_ext R
  intro r
  apply LinearMap.ext
  intro z
  change L_PO (L_MN (lof R ℕ M i x ⊗ₜ[R] lof R ℕ N j y) ⊗ₜ[R] lof R ℕ O r z) =
    a (L_MQ (lof R ℕ M i x ⊗ₜ[R]
      L_NO (lof R ℕ N j y ⊗ₜ[R] lof R ℕ O r z)))
  rw [hMN i j (i + j) rfl x y, hNO j r (j + r) rfl y z,
    hPO (i + j) r (i + j + r) rfl (F_MN i j (i + j) rfl x y) z,
    hMQ i (j + r) (i + j + r) (Nat.add_assoc i j r).symm x
      (F_NO j r (j + r) rfl y z), ha (i + j + r)]
  exact congrArg (lof R ℕ T (i + j + r)) (hassoc i j r x y z)

end DirectSum
