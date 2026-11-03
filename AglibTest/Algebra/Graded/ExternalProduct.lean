/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Graded.ExternalProduct

/-! Consumers retain independent graded-family universes and the native
signed tensor, with the original whole operational equations. -/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v₁ v₂ v₃

variable {R : Type u} [CommRing R]
  {M : ℕ → Type v₁} {N : ℕ → Type v₂} {P : ℕ → Type v₃}
  [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)]
  [DirectSum.GRing M] [DirectSum.GAlgebra R M]
  [DirectSum.GRing N] [DirectSum.GAlgebra R N]
  [DirectSum.GRing P] [DirectSum.GAlgebra R P]
  [GradedAlgebra (DirectSum.summandSubmodule (R := R) M)]
  [GradedAlgebra (DirectSum.summandSubmodule (R := R) N)]
  (cup : ∀ {p q n : ℕ}, p + q = n → P p →ₗ[R] P q →ₗ[R] P n)
  (hMul : ∀ {p q : ℕ} (x : P p) (y : P q),
    DirectSum.homogeneousInclusion (R := R) P p x *
        DirectSum.homogeneousInclusion (R := R) P q y =
      DirectSum.homogeneousInclusion (R := R) P (p + q) (cup rfl x y))
  (f : DirectSum ℕ M →ₐ[R] DirectSum ℕ P)
  (g : DirectSum ℕ N →ₐ[R] DirectSum ℕ P)
  (fDegree : ∀ n, M n →ₗ[R] P n) (gDegree : ∀ n, N n →ₗ[R] P n)
  (hf : ∀ n (x : M n), f (DirectSum.homogeneousInclusion (R := R) M n x) =
    DirectSum.homogeneousInclusion (R := R) P n (fDegree n x))
  (hg : ∀ n (y : N n), g (DirectSum.homogeneousInclusion (R := R) N n y) =
    DirectSum.homogeneousInclusion (R := R) P n (gDegree n y))
  (hComm : ∀ {p q n : ℕ} (h : p + q = n) (x : M p) (y : N q),
    cup h (fDegree p x) (gDegree q y) = ((-1 : ℤ) ^ (p * q)) •
      cup ((Nat.add_comm q p).trans h) (gDegree q y) (fDegree p x))

example : DirectSum.ExternalProductPureEq
    (DirectSum.externalProductAlgHom cup hMul f g fDegree gDegree hf hg hComm) f g :=
  DirectSum.externalProductAlgHom_pureEq cup hMul f g fDegree gDegree hf hg hComm

example (a : DirectSum ℕ M) (b : DirectSum ℕ N) :
    DirectSum.externalProductSourceEquiv (R := R) (M := M) (N := N) (a ⊗ₜ[R] b) =
      a ᵍ⊗ₜ[R] b :=
  DirectSum.externalProductSourceEquiv_tmul a b

example (a : DirectSum ℕ M) (b : DirectSum ℕ N) :
    DirectSum.externalProductAlgHom cup hMul f g fDegree gDegree hf hg hComm
      (a ᵍ⊗ₜ[R] b) = f a * g b :=
  DirectSum.externalProductAlgHom_tmul cup hMul f g fDegree gDegree hf hg hComm a b

example {p q n : ℕ} (h : p + q = n) :
    (DirectSum.externalProductAlgHom cup hMul f g fDegree gDegree hf hg hComm).toLinearMap ∘ₗ
        (GradedTensorProduct.of R (DirectSum.summandSubmodule (R := R) M)
          (DirectSum.summandSubmodule (R := R) N)).toLinearMap ∘ₗ
        TensorProduct.map (DirectSum.homogeneousInclusion (R := R) M p)
          (DirectSum.homogeneousInclusion (R := R) N q) =
      DirectSum.homogeneousInclusion (R := R) P n ∘ₗ
        TensorProduct.lift ((cup h).compl₁₂ (fDegree p) (gDegree q)) :=
  DirectSum.externalProductAlgHom_tensor cup hMul f g fDegree gDegree hf hg hComm h

section CanonicalInverse

variable
  (φ : GradedTensorProduct R (DirectSum.summandSubmodule (R := R) M)
    (DirectSum.summandSubmodule (R := R) N) →ₐ[R] DirectSum ℕ P)
  (e : (DirectSum ℕ M ⊗[R] DirectSum ℕ N) ≃ₗ[R] DirectSum ℕ P)
  (he : φ.toLinearMap ∘ₗ
      (DirectSum.externalProductSourceEquiv (R := R) (M := M) (N := N)).toLinearMap =
    e.toLinearMap)

example : (DirectSum.externalProductAlgEquiv φ e he).toAlgHom = φ :=
  DirectSum.externalProductAlgEquiv_toAlgHom φ e he

example (z : DirectSum ℕ P) : (DirectSum.externalProductAlgEquiv φ e he).symm z =
    DirectSum.externalProductSourceEquiv (R := R) (M := M) (N := N) (e.symm z) :=
  DirectSum.externalProductAlgEquiv_symm_apply φ e he z

end CanonicalInverse

variable (e : ∀ {p q n : ℕ}, p + q = n → M p →ₗ[R] N q →ₗ[R] P n)
  (he : ∀ {p q n : ℕ} (h : p + q = n) (x : M p) (y : N q),
    e h x y = cup h (fDegree p x) (gDegree q y))

example : DirectSum.ExternalProductHomogeneousEq
    (DirectSum.externalProductAlgHom cup hMul f g fDegree gDegree hf hg hComm) e :=
  DirectSum.externalProductAlgHom_homogeneousEq cup hMul f g fDegree gDegree hf hg hComm e he

example {p q n : ℕ} (h : p + q = n) (t : M p ⊗[R] N q →ₗ[R] P n)
    (ht : ∀ (x : M p) (y : N q), t (x ⊗ₜ[R] y) = e h x y) :
    (DirectSum.externalProductAlgHom cup hMul f g fDegree gDegree hf hg hComm).toLinearMap ∘ₗ
        (DirectSum.externalProductSourceEquiv (R := R) (M := M) (N := N)).toLinearMap ∘ₗ
        TensorProduct.map (DirectSum.homogeneousInclusion (R := R) M p)
          (DirectSum.homogeneousInclusion (R := R) N q) =
      DirectSum.homogeneousInclusion (R := R) P n ∘ₗ t :=
  DirectSum.ExternalProductHomogeneousEq.tensor
    (DirectSum.externalProductAlgHom_homogeneousEq cup hMul f g fDegree gDegree hf hg hComm e he)
    h t ht

example : DirectSum.externalProductSourceEquiv (R := R) (M := M) (N := N)
    ((1 : DirectSum ℕ M) ⊗ₜ[R] (1 : DirectSum ℕ N)) = 1 :=
  DirectSum.externalProductSourceEquiv_one


section ActualPhi

variable (Φ : GradedTensorProduct R (DirectSum.summandSubmodule (R := R) M)
    (DirectSum.summandSubmodule (R := R) N) →ₐ[R] DirectSum ℕ P)
  (hΦ : DirectSum.ExternalProductPureEq Φ f g)

example : DirectSum.ExternalProductHomogeneousEq Φ e :=
  hΦ.toHomogeneousEq cup hMul fDegree gDegree hf hg e he

example (s : (DirectSum ℕ M ⊗[R] DirectSum ℕ N) →ₗ[R]
      GradedTensorProduct R (DirectSum.summandSubmodule (R := R) M)
        (DirectSum.summandSubmodule (R := R) N))
    (hs : ∀ (a : DirectSum ℕ M) (b : DirectSum ℕ N), s (a ⊗ₜ[R] b) = a ᵍ⊗ₜ[R] b)
    {p q n : ℕ} (h : p + q = n) (T : M p ⊗[R] N q →ₗ[R] P n)
    (hT : ∀ (x : M p) (y : N q), T (x ⊗ₜ[R] y) = e h x y) :
    Φ.toLinearMap ∘ₗ s ∘ₗ TensorProduct.map
        (DirectSum.homogeneousInclusion (R := R) M p)
          (DirectSum.homogeneousInclusion (R := R) N q) =
      DirectSum.homogeneousInclusion (R := R) P n ∘ₗ T :=
  DirectSum.ExternalProductHomogeneousEq.tensorWithSource
    (hΦ.toHomogeneousEq cup hMul fDegree gDegree hf hg e he) s hs h T hT

end ActualPhi


section ActualAmbient

universe a b c m n p

variable {A : Type a} [Ring A] [Algebra R A]
  {B : Type b} [Ring B] [Algebra R B] {C : Type c} [Ring C] [Algebra R C]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜]
  {ℬ : ℕ → Submodule R B} [GradedAlgebra ℬ]
  {M₀ : ℕ → Type m} {N₀ : ℕ → Type n} {P₀ : ℕ → Type p}
  [∀ i, AddCommGroup (M₀ i)] [∀ i, Module R (M₀ i)]
  [∀ i, AddCommGroup (N₀ i)] [∀ i, Module R (N₀ i)]
  [∀ i, AddCommGroup (P₀ i)] [∀ i, Module R (P₀ i)]
  (I_M : ∀ i, M₀ i →ₗ[R] A) (I_N : ∀ i, N₀ i →ₗ[R] B) (I_P : ∀ i, P₀ i →ₗ[R] C)
  (hM : ∀ i (a : 𝒜 i), ∃ x : M₀ i, I_M i x = (a : A))
  (hN : ∀ i (b : ℬ i), ∃ y : N₀ i, I_N i y = (b : B))
  (cup₀ : ∀ {i j d : ℕ}, i + j = d → P₀ i →ₗ[R] P₀ j →ₗ[R] P₀ d)
  (hMul₀ : ∀ {i j : ℕ} (x : P₀ i) (y : P₀ j),
    I_P i x * I_P j y = I_P (i + j) (cup₀ rfl x y))
  (f₀ : A →ₐ[R] C) (g₀ : B →ₐ[R] C)
  (fDegree₀ : ∀ i, M₀ i →ₗ[R] P₀ i) (gDegree₀ : ∀ i, N₀ i →ₗ[R] P₀ i)
  (hf₀ : ∀ i (x : M₀ i), f₀ (I_M i x) = I_P i (fDegree₀ i x))
  (hg₀ : ∀ i (y : N₀ i), g₀ (I_N i y) = I_P i (gDegree₀ i y))
  (hComm₀ : ∀ {i j d : ℕ} (h : i + j = d) (x : M₀ i) (y : N₀ j),
    cup₀ h (fDegree₀ i x) (gDegree₀ j y) = ((-1 : ℤ) ^ (i * j)) •
      cup₀ ((Nat.add_comm j i).trans h) (gDegree₀ j y) (fDegree₀ i x))

example : GradedTensorProduct.ExternalProductPureEq
    (GradedTensorProduct.externalProductAlgHom I_M I_N I_P hM hN cup₀ hMul₀
      f₀ g₀ fDegree₀ gDegree₀ hf₀ hg₀ hComm₀) f₀ g₀ :=
  GradedTensorProduct.externalProductAlgHom_pureEq I_M I_N I_P hM hN cup₀ hMul₀
    f₀ g₀ fDegree₀ gDegree₀ hf₀ hg₀ hComm₀

example (Φ : GradedTensorProduct R 𝒜 ℬ →ₐ[R] C)
    (hΦ : GradedTensorProduct.ExternalProductPureEq Φ f₀ g₀)
    (e₀ : ∀ {i j d : ℕ}, i + j = d → M₀ i →ₗ[R] N₀ j →ₗ[R] P₀ d)
    (he₀ : ∀ {i j d : ℕ} (h : i + j = d) (x : M₀ i) (y : N₀ j),
      e₀ h x y = cup₀ h (fDegree₀ i x) (gDegree₀ j y))
    {i j d : ℕ} (h : i + j = d) (T : M₀ i ⊗[R] N₀ j →ₗ[R] P₀ d)
    (hT : ∀ x y, T (x ⊗ₜ[R] y) = e₀ h x y) :
    Φ.toLinearMap ∘ₗ
        (GradedTensorProduct.externalProductSourceEquiv (R := R) (𝒜 := 𝒜) (ℬ := ℬ)).toLinearMap ∘ₗ
        TensorProduct.map (I_M i) (I_N j) = I_P d ∘ₗ T :=
  GradedTensorProduct.ExternalProductHomogeneousEq.tensor I_M I_N I_P
    (GradedTensorProduct.ExternalProductPureEq.toHomogeneousEq I_M I_N I_P
      hΦ cup₀ hMul₀ fDegree₀ gDegree₀ hf₀ hg₀ e₀ he₀) h T hT

example : GradedTensorProduct.externalProductSourceEquiv (R := R) (𝒜 := 𝒜) (ℬ := ℬ)
    ((1 : A) ⊗ₜ[R] (1 : B)) = 1 :=
  GradedTensorProduct.externalProductSourceEquiv_one

end ActualAmbient
