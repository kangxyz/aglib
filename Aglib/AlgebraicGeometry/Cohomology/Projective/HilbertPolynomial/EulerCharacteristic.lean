/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Finiteness
public import Aglib.AlgebraicGeometry.Cohomology.Exact.AlternatingEuler
public import Mathlib.Algebra.BigOperators.Finprod
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom

/-!
# Euler characteristics on projective space over a field

For a field `k`, `projectiveEulerChar k ι M` is the alternating sum of the dimensions of
the original cohomology `Sheaf.H` of `M` on `ProjectiveSpace k ι`, with the structural
`k`-action through `toSpec`. For quasicoherent `M` and `ι ≃ Fin (n + 1)` it is the finite
sum over the degrees `q ≤ n`. It is invariant under isomorphism, vanishes on zero modules
and is additive on short exact sequences of coherent modules (Stacks, Tag 08AA): the
original long exact sequence, H⁰-injectivity and rank-nullity give a telescoping sum.

Dimension comparisons are stated once, at variable modules, for the original linear cohomology
maps `moduleCohomologyMapOfHom` with the structural constants: vanishing cohomology has
dimension zero, and for coherent modules the converse holds
(`projectiveCohomologyDim_eq_zero_iff`); a map surjective (injective) on `Hᵠ` does not increase
(decrease) `hᵠ` (`projectiveCohomologyDim_le_of_surjective`, `_le_of_injective`), and a
surjective one keeps it iff it is injective (`projectiveCohomologyDim_eq_iff_injective`). A
monomorphism does not decrease `h⁰` (`projectiveCohomologyDim_zero_le_of_mono`), and a module
with `H⁰ = 0` has no nonzero global sections (`unitHom_eq_zero_of_subsingleton`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology.QuotientEuler.ExactDimensions

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

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
  let : S.X₁.IsQuasicoherent := quasicoherent_of_affineCharts _ (fun A j _ => (h₁ A j).1)
  let : S.X₂.IsQuasicoherent := quasicoherent_of_affineCharts _ (fun A j _ => (h₂ A j).1)
  let : S.X₃.IsQuasicoherent := quasicoherent_of_affineCharts _ (fun A j _ => (h₃ A j).1)
  rw [projectiveEulerChar_eq_sum_range k ι n e S.X₁, projectiveEulerChar_eq_sum_range k ι n e S.X₂,
    projectiveEulerChar_eq_sum_range k ι n e S.X₃]
  exact moduleCohomology_alternatingSum_add (ProjectiveSpace k ι) (projectiveConstants k ι) S hS
    (projectiveCohomology_finite k ι n e S.X₁ h₁)
    (projectiveCohomology_finite k ι n e S.X₂ h₂)
    (projectiveCohomology_finite k ι n e S.X₃ h₃) n
    (projectiveCohomology_subsingleton_of_gt k ι n e S.X₁ (n + 1) (Nat.lt_succ_self n))

/-! ### Dimension comparisons -/

section Dimension

variable {k ι}

/-- Vanishing cohomology has dimension zero. -/
theorem projectiveCohomologyDim_eq_zero_of_subsingleton {M : (ProjectiveSpace k ι).Modules}
    {q : ℕ} (h : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace k ι) M) q)) :
    projectiveCohomologyDim k ι M q = 0 := by
  unfold projectiveCohomologyDim
  let := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) M q
  exact Module.finrank_zero_of_subsingleton

/-- Coherent cohomology of dimension zero vanishes. -/
theorem subsingleton_of_projectiveCohomologyDim_eq_zero (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M : (ProjectiveSpace k ι).Modules} (hM : affineLocallyFiniteType (ProjectiveSpace k ι) M)
    {q : ℕ} (h : projectiveCohomologyDim k ι M q = 0) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace k ι) M) q) := by
  let := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) M q
  have := projectiveCohomology_finite k ι n e M hM q
  exact Module.finrank_zero_iff.mp h

/-- Coherent cohomology has dimension zero iff it vanishes. -/
theorem projectiveCohomologyDim_eq_zero_iff (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M : (ProjectiveSpace k ι).Modules} (hM : affineLocallyFiniteType (ProjectiveSpace k ι) M)
    (q : ℕ) : projectiveCohomologyDim k ι M q = 0 ↔
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace k ι) M) q) :=
  ⟨subsingleton_of_projectiveCohomologyDim_eq_zero n e hM,
    projectiveCohomologyDim_eq_zero_of_subsingleton⟩

/-- A map that is surjective on `Hᵠ` does not increase `hᵠ`, for a coherent source. -/
theorem projectiveCohomologyDim_le_of_surjective (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M N : (ProjectiveSpace k ι).Modules} (f : M ⟶ N) (q : ℕ)
    (hM : affineLocallyFiniteType (ProjectiveSpace k ι) M)
    (hf : letI := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) M q
      letI := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) N q
      Function.Surjective
        (moduleCohomologyMapOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) f q)) :
    projectiveCohomologyDim k ι N q ≤ projectiveCohomologyDim k ι M q := by
  let := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) M q
  let := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) N q
  have := projectiveCohomology_finite k ι n e M hM q
  exact LinearMap.finrank_le_finrank_of_surjective hf

/-- A map that is injective on `Hᵠ` does not decrease `hᵠ`, for a coherent target. -/
theorem projectiveCohomologyDim_le_of_injective (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M N : (ProjectiveSpace k ι).Modules} (f : M ⟶ N) (q : ℕ)
    (hN : affineLocallyFiniteType (ProjectiveSpace k ι) N)
    (hf : letI := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) M q
      letI := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) N q
      Function.Injective
        (moduleCohomologyMapOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) f q)) :
    projectiveCohomologyDim k ι M q ≤ projectiveCohomologyDim k ι N q := by
  let := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) M q
  let := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) N q
  have := projectiveCohomology_finite k ι n e N hN q
  exact LinearMap.finrank_le_finrank_of_injective hf

/-- A map that is surjective on `Hᵠ` between coherent modules keeps `hᵠ` iff it is injective on
`Hᵠ`. -/
theorem projectiveCohomologyDim_eq_iff_injective (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M N : (ProjectiveSpace k ι).Modules} (f : M ⟶ N) (q : ℕ)
    (hM : affineLocallyFiniteType (ProjectiveSpace k ι) M)
    (hN : affineLocallyFiniteType (ProjectiveSpace k ι) N)
    (hf : letI := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) M q
      letI := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) N q
      Function.Surjective
        (moduleCohomologyMapOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) f q)) :
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) M q
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) N q
    projectiveCohomologyDim k ι N q = projectiveCohomologyDim k ι M q ↔
      Function.Injective
        (moduleCohomologyMapOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) f q) := by
  let := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) M q
  let := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι) N q
  have := projectiveCohomology_finite k ι n e M hM q
  have := projectiveCohomology_finite k ι n e N hN q
  constructor
  · intro h
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h.symm).mpr hf
  · intro hinj
    exact (LinearEquiv.ofBijective _ ⟨hinj, hf⟩).finrank_eq.symm

/-- `h⁰` does not decrease along a monomorphism into a coherent module. -/
theorem projectiveCohomologyDim_zero_le_of_mono (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M N : (ProjectiveSpace k ι).Modules} (j : M ⟶ N) [Mono j]
    (hN : affineLocallyFiniteType (ProjectiveSpace k ι) N) :
    projectiveCohomologyDim k ι M 0 ≤ projectiveCohomologyDim k ι N 0 :=
  projectiveCohomologyDim_le_of_injective n e j 0 hN
    (moduleH0MapOfHom_injective (ProjectiveSpace k ι) (projectiveConstants k ι) j)

-- Global sections of a module, as additive and as module sections, agree only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- A module whose `H⁰` vanishes has no nonzero global sections. -/
theorem unitHom_eq_zero_of_subsingleton {M : (ProjectiveSpace k ι).Modules}
    (h : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace k ι) M) 0))
    (s : SheafOfModules.unit (ProjectiveSpace k ι).ringCatSheaf ⟶ M) : s = 0 := by
  have hΓ : Subsingleton Γ(M, ⊤) :=
    (Sheaf.H.equiv₀ (moduleAddSheaf (ProjectiveSpace k ι) M)
      isTerminalTop).symm.injective.subsingleton
  apply (Scheme.Modules.unitHomGlobalSectionsAddEquiv (ProjectiveSpace k ι) M).injective
  rw [map_zero]
  exact Subsingleton.elim _ _

end Dimension

end AlgebraicGeometry.Scheme.Cohomology
