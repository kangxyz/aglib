/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AssociatedGraded.BoundedGeneration
public import Aglib.RingTheory.TensorProduct.CommutingActions
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Positive-degree generation over an affine tensor coefficient ring

The total module is finite over `B ⊗[A] S`, not necessarily over `S`. The proof
uses tensor induction and the original homogeneous decomposition of `S`.
It does not require a separate grading implementation on the tensor ring.
-/

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

/-- Original degree projection and inclusion, linear over the affine base. -/
def coefficientDegreeProjection (j : ℕ) : (⨁ n, M n) →ₗ[B] (⨁ n, M n) :=
  (DirectSum.lof B ℕ M j).comp (DirectSum.component B ℕ M j)

@[simp]
theorem coefficientDegreeProjection_of (j : ℕ) (x : M j) :
    coefficientDegreeProjection B M j (DirectSum.of M j x) = DirectSum.of M j x := by
  change DirectSum.of M j (DirectSum.of M j x j) = _
  simp

@[simp]
theorem coefficientDegreeProjection_of_ne {j n : ℕ} (h : n ≠ j) (x : M n) :
    coefficientDegreeProjection B M j (DirectSum.of M n x) = 0 := by
  change DirectSum.of M j (DirectSum.of M n x j) = 0
  rw [DirectSum.of_apply]
  simp [h]

/-- Positive homogeneous scalar products in a fixed total degree, spanned
over the actual affine coordinate ring rather than the original base ring. -/
def tensorPositiveDegreeSpan (c j : ℕ) : Submodule B (⨁ n, M n) :=
  Submodule.span B {z | ∃ r n, r + n = j ∧ 0 < r ∧ n ≤ c ∧
    ∃ a : G r, ∃ y : M n, z = (a : S) • DirectSum.of M n y}

variable (hgraded : ∀ r n (a : G r) (y : M n), ∃ z : M (r + n),
  (a : S) • DirectSum.of M n y = DirectSum.of M (r + n) z)

include hgraded

omit [Algebra A B] [Module (B ⊗[A] S) (⨁ n, M n)] in
private theorem coefficientDegreeProjection_smul_mem
    {c j n : ℕ} (hcj : c < j) (hn : n ≤ c) (s : S) (y : M n) :
    coefficientDegreeProjection B M j (s • DirectSum.of M n y) ∈
      tensorPositiveDegreeSpan A B S G M c j := by
  induction s using DirectSum.Decomposition.inductionOn G with
  | zero => simp only [zero_smul, map_zero]; exact Submodule.zero_mem _
  | @homogeneous r a =>
    obtain ⟨z, hz⟩ := hgraded r n a y
    by_cases h : r + n = j
    · have hr : 0 < r := by omega
      have he : coefficientDegreeProjection B M j ((a : S) • DirectSum.of M n y) =
          (a : S) • DirectSum.of M n y := by
        rw [hz]
        subst j
        exact coefficientDegreeProjection_of B M _ _
      rw [he]
      exact Submodule.subset_span ⟨r, n, h, hr, hn, a, y, rfl⟩
    · rw [hz, coefficientDegreeProjection_of_ne B M h]
      exact Submodule.zero_mem _
  | add s t hs ht =>
    rw [add_smul, map_add]
    exact Submodule.add_mem _ hs ht

variable (htmul : ∀ (b : B) (s : S) (x : ⨁ n, M n),
  (b ⊗ₜ[A] s) • x = b • s • x)

include htmul

private theorem coefficientDegreeProjection_tensor_smul_mem
    {c j n : ℕ} (hcj : c < j) (hn : n ≤ c) (t : B ⊗[A] S) (y : M n) :
    coefficientDegreeProjection B M j (t • DirectSum.of M n y) ∈
      tensorPositiveDegreeSpan A B S G M c j := by
  induction t using TensorProduct.inductionOn with
  | tmul b s =>
    rw [htmul, map_smul]
    exact Submodule.smul_mem _ b
      (coefficientDegreeProjection_smul_mem A B S G M hgraded hcj hn s y)
  | add s t hs ht =>
    rw [add_smul, map_add]
    exact Submodule.add_mem _ hs ht

/-- Tensor-ring finite generation supplies bounded homogeneous generation
and hence positive-degree scalar generation in every higher degree. The
finite-module hypothesis is over the actual extended coefficient ring. -/
theorem exists_tensorPositiveDegreeSpan [Module.Finite (B ⊗[A] S) (⨁ n, M n)] :
    ∃ c : ℕ, ∀ j, c < j → ∀ x : M j,
      DirectSum.of M j x ∈ tensorPositiveDegreeSpan A B S G M c j := by
  classical
  obtain ⟨c, hc⟩ := exists_boundedDegreeSpan_eq_top (B ⊗[A] S) M
  refine ⟨c, fun j hj x => ?_⟩
  let T : Set (⨁ n, M n) :=
    {z | ∃ n ≤ c, ∃ y : M n, z = DirectSum.of M n y}
  have hx : DirectSum.of M j x ∈ Submodule.span (B ⊗[A] S) T := by
    change DirectSum.of M j x ∈ boundedDegreeSpan (B ⊗[A] S) M c
    rw [hc]
    exact Submodule.mem_top
  obtain ⟨l, hl⟩ := (Finsupp.mem_span_iff_linearCombination (B ⊗[A] S) T _).mp hx
  have hp : coefficientDegreeProjection B M j (Finsupp.linearCombination (B ⊗[A] S)
      ((↑) : T → (⨁ n, M n)) l) ∈ tensorPositiveDegreeSpan A B S G M c j := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    apply Submodule.sum_mem
    intro z _
    obtain ⟨n, hn, y, hy⟩ := z.property
    rw [hy]
    exact coefficientDegreeProjection_tensor_smul_mem A B S G M hgraded htmul hj hn (l z) y
  simpa only [hl, coefficientDegreeProjection_of] using hp

end GradedModule
