/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Graded.TensorProduct.PointNaturality

/-! # Exact inputs for the existing whole tensor coherence proofs

The records contain the supplied cup maps, degreewise pullbacks and their
geometric compatibility. Their diagram methods reuse the complete generic proofs.
-/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum

universe u m n o p q s t m' n' p'

namespace DirectSum

variable {R : Type u} [Field R]

section Naturality

variable (M : ℕ → Type m) (N : ℕ → Type n) (P : ℕ → Type p)
  (M' : ℕ → Type m') (N' : ℕ → Type n') (P' : ℕ → Type p')
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
  [∀ i, AddCommMonoid (M' i)] [∀ i, Module R (M' i)]
  [∀ i, AddCommMonoid (N' i)] [∀ i, Module R (N' i)]
  [∀ i, AddCommMonoid (P' i)] [∀ i, Module R (P' i)]

/-- The exact operator inputs and original degreewise naturality law. -/
structure NaturalityInputs where
  /-- The given cup maps on the source cohomology families. -/
  cup : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d
  /-- The given cup maps on the target cohomology families. -/
  cup' : ∀ i j d, i + j = d → M' i →ₗ[R] N' j →ₗ[R] P' d
  /-- The original degreewise pullbacks on the first factor. -/
  leftPullback : ∀ i, M i →ₗ[R] M' i
  /-- The original degreewise pullbacks on the second factor. -/
  rightPullback : ∀ j, N j →ₗ[R] N' j
  /-- The original degreewise pullbacks on the product. -/
  productPullback : ∀ d, P d →ₗ[R] P' d
  /-- The supplied geometric compatibility of these same maps. -/
  compatibility : ∀ i j d (h : i + j = d) (x : M i) (y : N j),
    productPullback d (cup i j d h x y) =
      cup' i j d h (leftPullback i x) (rightPullback j y)

namespace NaturalityInputs

variable {M N P M' N' P'}

/-- The existing whole naturality diagram on these exact input fields. -/
def Diagram (input : NaturalityInputs (R := R) M N P M' N' P') : Prop :=
  tensorNaturalityDiagram (R := R) M N P M' N' P' input.cup input.cup'
    input.leftPullback input.rightPullback input.productPullback

/-- The existing complete proof applies to the supplied original compatibility. -/
theorem diagram (input : NaturalityInputs (R := R) M N P M' N' P') : input.Diagram := by
  exact tensorNaturalityDiagramOfValues (R := R) M N P M' N' P'
    input.cup input.cup' input.leftPullback input.rightPullback input.productPullback
    input.compatibility

/-- Express the naturality diagram using the supplied original total maps. -/
theorem diagramWithMaps (input : NaturalityInputs (R := R) M N P M' N' P')
    (L : (DirectSum ℕ M ⊗[R] DirectSum ℕ N) →ₗ[R] DirectSum ℕ P)
    (L' : (DirectSum ℕ M' ⊗[R] DirectSum ℕ N') →ₗ[R] DirectSum ℕ P')
    (p : DirectSum ℕ P →ₗ[R] DirectSum ℕ P')
    (f : DirectSum ℕ M →ₗ[R] DirectSum ℕ M') (g : DirectSum ℕ N →ₗ[R] DirectSum ℕ N')
    (hL : L = canonicalTotalCupMap M N P input.cup)
    (hL' : L' = canonicalTotalCupMap M' N' P' input.cup')
    (hp : p = lmap input.productPullback)
    (hf : f = lmap input.leftPullback) (hg : g = lmap input.rightPullback) :
    p ∘ₗ L = L' ∘ₗ TensorProduct.map f g := by
  rw [hL, hL', hp, hf, hg]
  exact input.diagram

end NaturalityInputs

end Naturality

section Associativity

variable (M : ℕ → Type m) (N : ℕ → Type n) (O : ℕ → Type o)
  (P : ℕ → Type p) (Q : ℕ → Type q) (S : ℕ → Type s) (T : ℕ → Type t)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommMonoid (O i)] [∀ i, Module R (O i)]
  [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
  [∀ i, AddCommMonoid (Q i)] [∀ i, Module R (Q i)]
  [∀ i, AddCommMonoid (S i)] [∀ i, Module R (S i)]
  [∀ i, AddCommMonoid (T i)] [∀ i, Module R (T i)]

/-- The exact four cup families and original associator compatibility. -/
structure AssociativityInputs where
  /-- The given cup maps for the first two factors. -/
  cupMN : ∀ i j d, i + j = d → M i →ₗ[R] N j →ₗ[R] P d
  /-- The given cup maps for their product and the third factor. -/
  cupPO : ∀ d r n, d + r = n → P d →ₗ[R] O r →ₗ[R] T n
  /-- The given cup maps for the last two factors. -/
  cupNO : ∀ j r d, j + r = d → N j →ₗ[R] O r →ₗ[R] Q d
  /-- The given cup maps for the first factor and that product. -/
  cupMQ : ∀ i d n, i + d = n → M i →ₗ[R] Q d →ₗ[R] S n
  /-- The original degreewise associator pullbacks. -/
  pullback : ∀ n, S n →ₗ[R] T n
  /-- The supplied geometric associativity law on these same fields. -/
  compatibility : ∀ i j r (x : M i) (y : N j) (z : O r),
    pullback (i + j + r)
        (cupMQ i (j + r) (i + j + r) (Nat.add_assoc i j r).symm x
          (cupNO j r (j + r) rfl y z)) =
      cupPO (i + j) r (i + j + r) rfl (cupMN i j (i + j) rfl x y) z

namespace AssociativityInputs

variable {M N O P Q S T}

/-- The existing whole associativity diagram on these exact input fields. -/
def Diagram (input : AssociativityInputs (R := R) M N O P Q S T) : Prop :=
  tensorAssociativityDiagram (R := R) M N O P Q S T
    input.cupMN input.cupPO input.cupNO input.cupMQ input.pullback

/-- The existing complete proof applies to the supplied original geometric law. -/
theorem diagram (input : AssociativityInputs (R := R) M N O P Q S T) : input.Diagram := by
  exact tensorAssociativityDiagramOfValues (R := R) M N O P Q S T
    input.cupMN input.cupPO input.cupNO input.cupMQ input.pullback input.compatibility

/-- Express the associativity diagram using the supplied original total maps. -/
theorem diagramWithMaps (input : AssociativityInputs (R := R) M N O P Q S T)
    (Lmn : (DirectSum ℕ M ⊗[R] DirectSum ℕ N) →ₗ[R] DirectSum ℕ P)
    (Lpo : (DirectSum ℕ P ⊗[R] DirectSum ℕ O) →ₗ[R] DirectSum ℕ T)
    (Lno : (DirectSum ℕ N ⊗[R] DirectSum ℕ O) →ₗ[R] DirectSum ℕ Q)
    (Lmq : (DirectSum ℕ M ⊗[R] DirectSum ℕ Q) →ₗ[R] DirectSum ℕ S)
    (a : DirectSum ℕ S →ₗ[R] DirectSum ℕ T)
    (hmn : Lmn = canonicalTotalCupMap M N P input.cupMN)
    (hpo : Lpo = canonicalTotalCupMap P O T input.cupPO)
    (hno : Lno = canonicalTotalCupMap N O Q input.cupNO)
    (hmq : Lmq = canonicalTotalCupMap M Q S input.cupMQ)
    (ha : a = lmap input.pullback) :
    Lpo ∘ₗ Lmn.rTensor (DirectSum ℕ O) =
      a ∘ₗ Lmq ∘ₗ Lno.lTensor (DirectSum ℕ M) ∘ₗ
        (TensorProduct.assoc R (DirectSum ℕ M) (DirectSum ℕ N) (DirectSum ℕ O)).toLinearMap := by
  rw [hmn, hpo, hno, hmq, ha]
  exact input.diagram

end AssociativityInputs

end Associativity

end DirectSum
