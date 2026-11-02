/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Exact.Euler
public import Aglib.AlgebraicGeometry.Cohomology.Exact.Modules

/-! # Alternating sums of original module cohomology

The actual scalar-linear coefficient maps and connecting maps give all three
rank-nullity identities. Their complete alternating-sum construction is made
over an arbitrary scheme, before any projective-space specialization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Cohomology.QuotientEuler.ExactDimensions

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Alternating sums along a long exact sequence telescope: if `b q = rf q + rg q`,
`c q = rg q + rd q`, `a (q + 1) = rd q + rf (q + 1)` and `a 0 = rf 0`, the alternating sum
of `b - a - c` up to degree `M` is `-(-1)^M rd M`. -/
theorem sum_range_alternating_of_long_exact (a b c rf rg rd : ℕ → ℕ)
    (h0 : a 0 = rf 0) (ha : ∀ q, a (q + 1) = rd q + rf (q + 1))
    (hb : ∀ q, b q = rf q + rg q) (hc : ∀ q, c q = rg q + rd q) (M : ℕ) :
    ∑ q ∈ Finset.range (M + 1), (-1 : ℤ) ^ q * ((b q : ℤ) - a q - c q) =
      -((-1 : ℤ) ^ M * rd M) := by
  induction M with
  | zero =>
    rw [Finset.sum_range_one, hb 0, h0, hc 0]
    push_cast
    ring
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, hb (M + 1), ha M, hc (M + 1)]
    push_cast
    ring

variable (X : Scheme.{u}) {k : Type u} [Field k] (α : k →+* Γ(X, ⊤))

/-- Finite rank of the original cohomology with its actual specified scalar action. -/
def moduleCohomologyDimOfHom (M : X.Modules) (q : ℕ) : ℕ :=
  letI := moduleCohomologyModuleOfHom X α M q
  Module.finrank k (Sheaf.H.{u + 1} (moduleAddSheaf X M) q)

/-- Finite original cohomology and vanishing of the next left term imply
additivity of the truncated alternating sum for the actual short exact sequence. -/
theorem moduleCohomology_alternatingSum_add (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₁ : ∀ q : ℕ, letI := moduleCohomologyModuleOfHom X α S.X₁ q
      Module.Finite k (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₁) q))
    (h₂ : ∀ q : ℕ, letI := moduleCohomologyModuleOfHom X α S.X₂ q
      Module.Finite k (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₂) q))
    (h₃ : ∀ q : ℕ, letI := moduleCohomologyModuleOfHom X α S.X₃ q
      Module.Finite k (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₃) q))
    (n : ℕ) (hvan : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₁) (n + 1))) :
    (∑ q ∈ Finset.range (n + 1), (-1 : ℤ) ^ q * (moduleCohomologyDimOfHom X α S.X₂ q : ℤ)) =
      (∑ q ∈ Finset.range (n + 1), (-1 : ℤ) ^ q * (moduleCohomologyDimOfHom X α S.X₁ q : ℤ)) +
      (∑ q ∈ Finset.range (n + 1), (-1 : ℤ) ^ q * (moduleCohomologyDimOfHom X α S.X₃ q : ℤ)) := by
  have := hS.mono_f
  let rf : ℕ → ℕ := fun q => by
    letI := moduleCohomologyModuleOfHom X α S.X₁ q
    letI := moduleCohomologyModuleOfHom X α S.X₂ q
    exact Module.finrank k (LinearMap.range (moduleCohomologyMapOfHom X α S.f q))
  let rg : ℕ → ℕ := fun q => by
    letI := moduleCohomologyModuleOfHom X α S.X₂ q
    letI := moduleCohomologyModuleOfHom X α S.X₃ q
    exact Module.finrank k (LinearMap.range (moduleCohomologyMapOfHom X α S.g q))
  let rd : ℕ → ℕ := fun q => by
    letI := moduleCohomologyModuleOfHom X α S.X₃ q
    letI := moduleCohomologyModuleOfHom X α S.X₁ (q + 1)
    exact Module.finrank k (LinearMap.range (moduleCohomologyConnectingOfHom X α S hS q))
  have h0 : moduleCohomologyDimOfHom X α S.X₁ 0 = rf 0 := by
    let := moduleCohomologyModuleOfHom X α S.X₁ 0
    let := moduleCohomologyModuleOfHom X α S.X₂ 0
    exact (range_finrank_of_injective _ (moduleH0MapOfHom_injective X α S.f)).symm
  have ha (q : ℕ) : moduleCohomologyDimOfHom X α S.X₁ (q + 1) = rd q + rf (q + 1) := by
    let := moduleCohomologyModuleOfHom X α S.X₃ q
    let := moduleCohomologyModuleOfHom X α S.X₁ (q + 1)
    let := moduleCohomologyModuleOfHom X α S.X₂ (q + 1)
    have := h₁ (q + 1)
    have h := exact_dimensions _ _ (moduleCohomologyConnectingOfHom_exact_right X α S hS q)
    exact h.symm.trans (Nat.add_comm _ _)
  have hb (q : ℕ) : moduleCohomologyDimOfHom X α S.X₂ q = rf q + rg q := by
    let := moduleCohomologyModuleOfHom X α S.X₁ q
    let := moduleCohomologyModuleOfHom X α S.X₂ q
    let := moduleCohomologyModuleOfHom X α S.X₃ q
    have := h₂ q
    have h := exact_dimensions _ _ (moduleCohomologyMapOfHom_exact X α S hS q)
    exact h.symm.trans (Nat.add_comm _ _)
  have hc (q : ℕ) : moduleCohomologyDimOfHom X α S.X₃ q = rg q + rd q := by
    let := moduleCohomologyModuleOfHom X α S.X₂ q
    let := moduleCohomologyModuleOfHom X α S.X₃ q
    let := moduleCohomologyModuleOfHom X α S.X₁ (q + 1)
    have := h₃ q
    have h := exact_dimensions _ _ (moduleCohomologyConnectingOfHom_exact_left X α S hS q)
    exact h.symm.trans (Nat.add_comm _ _)
  have hrd : rd n = 0 := by
    have h := ha n
    have hz : moduleCohomologyDimOfHom X α S.X₁ (n + 1) = 0 := by
      let := moduleCohomologyModuleOfHom X α S.X₁ (n + 1)
      have := hvan
      exact Module.finrank_zero_of_subsingleton
    rw [hz] at h
    omega
  have key := sum_range_alternating_of_long_exact _ _ _ rf rg rd h0 ha hb hc n
  rw [hrd, Nat.cast_zero, mul_zero, neg_zero] at key
  simp only [mul_sub, Finset.sum_sub_distrib] at key
  linarith

end AlgebraicGeometry.Scheme.Cohomology
