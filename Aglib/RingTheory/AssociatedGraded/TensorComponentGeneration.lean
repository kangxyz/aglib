/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AssociatedGraded.TensorPositiveGeneration

/-! # Bounded positive generation on the original homogeneous components -/

@[expose] public noncomputable section
open DirectSum
open scoped TensorProduct
namespace GradedModule
universe u v w z
variable (A : Type u) (B : Type v) (S : Type w)
  [CommRing A] [CommRing B] [CommRing S] [Algebra A B] [Algebra A S]
  (G : ℕ → Submodule A S) [DirectSum.Decomposition G]
  (M : ℕ → Type z) [∀ n, AddCommGroup (M n)] [∀ n, Module B (M n)]
  [Module S (⨁ n, M n)] [Module (B ⊗[A] S) (⨁ n, M n)]
  (μ : ∀ r n, G r → M n → M (r + n))

/-- Positive products as a set in the original single homogeneous component. -/
def positiveComponentProducts (c j : ℕ) : Set (M j) :=
  {z | ∃ r n, ∃ h : r + n = j, 0 < r ∧ n ≤ c ∧
    ∃ (a : G r) (y : M n), z = h ▸ μ r n a y}

variable (hμ : ∀ r n (a : G r) (y : M n),
  (a : S) • DirectSum.of M n y = DirectSum.of M (r + n) (μ r n a y))

include hμ

omit [Algebra A B] [DirectSum.Decomposition G]
    [Module (B ⊗[A] S) (⨁ n, M n)] in
/-- Projecting the actual positive span gives the actual component span. -/
theorem mem_span_positiveComponentProducts {c j : ℕ} (x : M j)
    (hx : DirectSum.of M j x ∈ tensorPositiveDegreeSpan A B S G M c j) :
    x ∈ Submodule.span B (positiveComponentProducts A S G M μ c j) := by
  have hle : tensorPositiveDegreeSpan A B S G M c j ≤
      (Submodule.span B (positiveComponentProducts A S G M μ c j)).comap
        (DirectSum.component B ℕ M j) := by
    apply Submodule.span_le.mpr
    intro z hz
    obtain ⟨r, n, he, hr, hn, a, y, rfl⟩ := hz
    change DirectSum.component B ℕ M j ((a : S) • DirectSum.of M n y) ∈
      Submodule.span B (positiveComponentProducts A S G M μ c j)
    rw [hμ]
    subst j
    have hp : μ r n a y ∈ Submodule.span B
        (positiveComponentProducts A S G M μ c (r + n)) :=
      Submodule.subset_span ⟨r, n, rfl, hr, hn, a, y, rfl⟩
    change DirectSum.of M (r + n) (μ r n a y) (r + n) ∈
      Submodule.span B (positiveComponentProducts A S G M μ c (r + n))
    simpa using hp
  have hp := hle hx
  change DirectSum.of M j x j ∈
    Submodule.span B (positiveComponentProducts A S G M μ c j) at hp
  simpa using hp

/-- Finite generation over the actual tensor coefficient ring gives one
bound after which positive products span each original component. -/
theorem exists_span_positiveComponentProducts
    (htmul : ∀ (b : B) (s : S) (x : ⨁ n, M n), (b ⊗ₜ[A] s) • x = b • s • x)
    [Module.Finite (B ⊗[A] S) (⨁ n, M n)] :
    ∃ c : ℕ, ∀ j, c < j →
      Submodule.span B (positiveComponentProducts A S G M μ c j) = ⊤ := by
  obtain ⟨c, hc⟩ := exists_tensorPositiveDegreeSpan A B S G M
    (fun r n a y => ⟨μ r n a y, hμ r n a y⟩) htmul
  refine ⟨c, fun j hj => top_unique ?_⟩
  intro x _
  exact mem_span_positiveComponentProducts A B S G M μ hμ x (hc j hj x)

end GradedModule
