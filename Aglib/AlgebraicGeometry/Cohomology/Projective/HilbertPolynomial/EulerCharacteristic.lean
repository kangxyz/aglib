/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Finiteness
public import Aglib.AlgebraicGeometry.Cohomology.Exact.Euler
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Euler characteristics on projective space over a field

For a field `k`, `projectiveEulerChar k ι M` is the alternating sum of the dimensions of
the original cohomology `Sheaf.H` of `M` on `ProjectiveSpace k ι`, with the structural
`k`-action through `toSpec`. For quasicoherent `M` and `ι ≃ Fin (n + 1)` it is the finite
sum over the degrees `q ≤ n`. It is invariant under isomorphism, vanishes on zero modules
and is additive on short exact sequences of coherent modules (Stacks, Tag 08AA): the
original long exact sequence, H⁰-injectivity and rank-nullity give a telescoping sum.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
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

variable (k : Type u) [Field k] (ι : Type u)

/-- The structural constants of projective space over a field. -/
abbrev projectiveConstants : k →+* Γ(ProjectiveSpace k ι, ⊤) :=
  (toSpec k ι).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- The dimension of original cohomology for the structural `k`-action. Native `finrank` is
zero if the cohomology is not finite-dimensional; for coherent `M` it is finite by
`projectiveCohomology_finite` (`Cohomology/Projective/Finiteness.lean`). -/
def projectiveCohomologyDim (M : (ProjectiveSpace k ι).Modules) (q : ℕ) : ℕ :=
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) M q
  Module.finrank k (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace k ι) M) q)

/-- The Euler characteristic: the alternating sum of original cohomology dimensions.
Native `finsum` is zero if its support is infinite. For quasicoherent `M`, with
`ι ≃ Fin (n + 1)`, the cohomology vanishes above degree `n` by
`projectiveCohomology_subsingleton_of_gt` (`Cohomology/Projective/Vanishing.lean`), so the
sum is the finite alternating sum `projectiveEulerChar_eq_sum_range`; for coherent `M` its
terms are finite dimensions. -/
def projectiveEulerChar (M : (ProjectiveSpace k ι).Modules) : ℤ :=
  ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * (projectiveCohomologyDim k ι M q : ℤ)

/-- Isomorphic modules have the same cohomology dimensions. -/
theorem projectiveCohomologyDim_congr {M N : (ProjectiveSpace k ι).Modules} (e : M ≅ N)
    (q : ℕ) : projectiveCohomologyDim k ι M q = projectiveCohomologyDim k ι N q :=
  ((moduleCohomologyFunctorOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) q).mapIso
    e).toLinearEquiv.finrank_eq

/-- Zero modules have zero cohomology dimensions. -/
theorem projectiveCohomologyDim_of_isZero {M : (ProjectiveSpace k ι).Modules} (hM : IsZero M)
    (q : ℕ) : projectiveCohomologyDim k ι M q = 0 := by
  unfold projectiveCohomologyDim
  let := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) M q
  have h := (moduleCohomologyFunctorOfHom (ProjectiveSpace k ι)
    (projectiveConstants k ι) q).map_isZero hM
  have : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace k ι) M) q) :=
    ModuleCat.isZero_iff_subsingleton.mp h
  exact Module.finrank_zero_of_subsingleton

/-- Cohomology dimensions of quasicoherent modules vanish above the projective dimension. -/
theorem projectiveCohomologyDim_eq_zero_of_lt (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace k ι).Modules) [M.IsQuasicoherent] {q : ℕ} (hq : n < q) :
    projectiveCohomologyDim k ι M q = 0 := by
  let := Fintype.ofEquiv (Fin (n + 1)) e.symm
  have := projectiveCohomology_subsingleton_of_gt k ι n e M q hq
  unfold projectiveCohomologyDim
  let := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) M q
  exact Module.finrank_zero_of_subsingleton

/-- For quasicoherent modules the Euler characteristic is the finite sum up to degree `n`. -/
theorem projectiveEulerChar_eq_sum_range (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace k ι).Modules) [M.IsQuasicoherent] :
    projectiveEulerChar k ι M = ∑ q ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ q * (projectiveCohomologyDim k ι M q : ℤ) := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro q hq
  by_contra h
  have hn : n < q := by
    have : ¬q < n + 1 := by simpa only [Finset.mem_coe, Finset.mem_range] using h
    omega
  exact hq (by simp only [projectiveCohomologyDim_eq_zero_of_lt k ι n e M hn, Nat.cast_zero,
    mul_zero])

/-- The Euler characteristic is invariant under isomorphism. -/
theorem projectiveEulerChar_congr {M N : (ProjectiveSpace k ι).Modules} (e : M ≅ N) :
    projectiveEulerChar k ι M = projectiveEulerChar k ι N := by
  simp only [projectiveEulerChar, projectiveCohomologyDim_congr k ι e]

/-- Zero modules have zero Euler characteristic. -/
theorem projectiveEulerChar_of_isZero {M : (ProjectiveSpace k ι).Modules} (hM : IsZero M) :
    projectiveEulerChar k ι M = 0 := by
  simp only [projectiveEulerChar, projectiveCohomologyDim_of_isZero k ι hM, Nat.cast_zero,
    mul_zero, finsum_zero]

/-- Additivity of the Euler characteristic on short exact sequences of coherent modules. -/
theorem projectiveEulerChar_add_of_shortExact (n : ℕ) (e : ι ≃ Fin (n + 1))
    (S : ShortComplex (ProjectiveSpace k ι).Modules) (hS : S.ShortExact)
    (h₁ : affineLocallyFiniteType (ProjectiveSpace k ι) S.X₁)
    (h₂ : affineLocallyFiniteType (ProjectiveSpace k ι) S.X₂)
    (h₃ : affineLocallyFiniteType (ProjectiveSpace k ι) S.X₃) :
    projectiveEulerChar k ι S.X₂ =
      projectiveEulerChar k ι S.X₁ + projectiveEulerChar k ι S.X₃ := by
  let X := ProjectiveSpace k ι
  let α := projectiveConstants k ι
  let : S.X₁.IsQuasicoherent := quasicoherent_of_affineCharts _ (fun A j _ => (h₁ A j).1)
  let : S.X₂.IsQuasicoherent := quasicoherent_of_affineCharts _ (fun A j _ => (h₂ A j).1)
  let : S.X₃.IsQuasicoherent := quasicoherent_of_affineCharts _ (fun A j _ => (h₃ A j).1)
  have := hS.mono_f
  rw [projectiveEulerChar_eq_sum_range k ι n e S.X₁, projectiveEulerChar_eq_sum_range k ι n e S.X₂,
    projectiveEulerChar_eq_sum_range k ι n e S.X₃]
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
  have h0 : projectiveCohomologyDim k ι S.X₁ 0 = rf 0 := by
    let := moduleCohomologyModuleOfHom X α S.X₁ 0
    let := moduleCohomologyModuleOfHom X α S.X₂ 0
    exact (range_finrank_of_injective _ (moduleH0MapOfHom_injective X α S.f)).symm
  have ha (q : ℕ) : projectiveCohomologyDim k ι S.X₁ (q + 1) = rd q + rf (q + 1) := by
    let := moduleCohomologyModuleOfHom X α S.X₃ q
    let := moduleCohomologyModuleOfHom X α S.X₁ (q + 1)
    let := moduleCohomologyModuleOfHom X α S.X₂ (q + 1)
    have := projectiveCohomology_finite k ι n e S.X₁ h₁ (q + 1)
    have h := exact_dimensions _ _ (moduleCohomologyConnectingOfHom_exact_right X α S hS q)
    exact h.symm.trans (Nat.add_comm _ _)
  have hb (q : ℕ) : projectiveCohomologyDim k ι S.X₂ q = rf q + rg q := by
    let := moduleCohomologyModuleOfHom X α S.X₁ q
    let := moduleCohomologyModuleOfHom X α S.X₂ q
    let := moduleCohomologyModuleOfHom X α S.X₃ q
    have := projectiveCohomology_finite k ι n e S.X₂ h₂ q
    have h := exact_dimensions _ _ (moduleCohomologyMapOfHom_exact X α S hS q)
    exact h.symm.trans (Nat.add_comm _ _)
  have hc (q : ℕ) : projectiveCohomologyDim k ι S.X₃ q = rg q + rd q := by
    let := moduleCohomologyModuleOfHom X α S.X₂ q
    let := moduleCohomologyModuleOfHom X α S.X₃ q
    let := moduleCohomologyModuleOfHom X α S.X₁ (q + 1)
    have := projectiveCohomology_finite k ι n e S.X₃ h₃ q
    have h := exact_dimensions _ _ (moduleCohomologyConnectingOfHom_exact_left X α S hS q)
    exact h.symm.trans (Nat.add_comm _ _)
  have hrd : rd n = 0 := by
    have h := ha n
    rw [projectiveCohomologyDim_eq_zero_of_lt k ι n e S.X₁ (Nat.lt_succ_self n)] at h
    omega
  have key := sum_range_alternating_of_long_exact _ _ _ rf rg rd h0 ha hb hc n
  rw [hrd, Nat.cast_zero, mul_zero, neg_zero] at key
  simp only [mul_sub, Finset.sum_sub_distrib] at key
  linarith

end AlgebraicGeometry.Scheme.Cohomology
