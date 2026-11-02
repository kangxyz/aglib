/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Kunneth.MayerVietoris

/-! The actual shifted antidiagonal maps preserve original exactness over flat first factors. -/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum
open Kunneth.MayerVietoris

universe r m a b c

variable {R : Type r} [CommRing R]
  (M : ℕ → Type m) [∀ p, AddCommGroup (M p)] [∀ p, Module R (M p)]
  [∀ p, Module.Flat R (M p)]
  {A : ℕ → Type a} {B : ℕ → Type b} {C : ℕ → Type c}
  [∀ q, AddCommGroup (A q)] [∀ q, Module R (A q)]
  [∀ q, AddCommGroup (B q)] [∀ q, Module R (B q)]
  [∀ q, AddCommGroup (C q)] [∀ q, Module R (C q)]

example (f : ∀ q, A q →ₗ[R] B q) (δ : ∀ q, B q →ₗ[R] C (q + 1))
    (h : ∀ q, Function.Exact (f q) (δ q)) (n : ℕ) :
    Function.Exact (tensorMap (R := R) M f n) (tensorBoundary (R := R) M δ n) :=
  tensorMap_tensorBoundary_exact M f δ h n

example (δ : ∀ q, A q →ₗ[R] B (q + 1)) (f : ∀ q, B q →ₗ[R] C q)
    (h : ∀ q, Function.Exact (δ q) (f (q + 1))) (hzero : Function.Injective (f 0)) (n : ℕ) :
    Function.Exact (tensorBoundary (R := R) M δ n) (tensorMap (R := R) M f (n + 1)) :=
  tensorBoundary_tensorMap_exact M δ f h hzero n

example (δ : ∀ q, A q →ₗ[R] B (q + 1)) (n : ℕ) (s : HomologicalComplex₂.TotalDegree n)
    (x : M s.val.1 ⊗[R] A s.val.2) :
    tensorBoundary (R := R) M δ n (DirectSum.lof R _ _ s x) =
      DirectSum.lof R _ _ (rightSuccessor n s)
        (((-1 : R) ^ s.val.1) • (δ s.val.2).lTensor (M s.val.1) x) :=
  tensorBoundary_lof M δ n s x
