/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Regularity.Mumford.Bound
public import Aglib.AlgebraicGeometry.Cohomology.Projective.GlobalSections.Polynomial
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Coproduct
public import Aglib.RingTheory.MvPolynomial.Homogeneous

/-!
# The free module `O^p` is an ambient module of Mumford's induction

`isMumfordAmbient_twistingCoproduct`: a finite coproduct `∐_{i : I} O(0)` is coherent,
`0`-regular, and `h⁰(O(r) ⊗ O^I) ≤ |I| (r + 1)^{n+1}` for `r ≥ 0`. The `h⁰` bound counts
monomials: `H⁰(O(m))` is the degree-`m` homogeneous polynomials
(`twistingH0PolynomialLinearEquiv`), spanned by the monomials of degree `m`, each determined by
its exponents in `{0, …, m}` (`MvPolynomial.finrank_homogeneousSubmodule_le`). With this,
`isProjectiveRegular_mumfordBound_free_of_hasHyperplaneSections` is Nitsure, Thm 2.3
(arXiv:math/0504590v1, p. 11) for subsheaves of `O^p` over a field with hyperplane sections
(`HasHyperplaneSections`), and `_ideal_of_hasHyperplaneSections` is its case `p = 1`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {k : Type u} [Field k] {ι : Type u}

/-- `h⁰(O(m)) ≤ (m + 1)^{n+1}` on projective `n`-space. -/
theorem projectiveCohomologyDim_twistingSheaf_zero_le (n : ℕ) (e : ι ≃ Fin (n + 1)) (m : ℕ) :
    projectiveCohomologyDim k ι (twistingSheaf k ι (m : ℤ)) 0 ≤ (m + 1) ^ (n + 1) := by
  let := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) (projectiveConstants k ι)
    (twistingSheaf k ι (m : ℤ)) 0
  have h := (twistingH0PolynomialLinearEquiv k ι (e.symm 0) m).finrank_eq
  have hc : Fintype.card ι = n + 1 := by simp [Fintype.card_congr e]
  unfold projectiveCohomologyDim
  rw [h, ← hc]
  exact MvPolynomial.finrank_homogeneousSubmodule_le ι k m

/-- `h⁰` of a finite coproduct of twists `O(m)` is `|I| · h⁰(O(m))`. -/
theorem projectiveCohomologyDim_twistingCoproduct_zero (n : ℕ) (e : ι ≃ Fin (n + 1))
    {I : Type u} [Fintype I] (m : ℤ) :
    projectiveCohomologyDim k ι (∐ fun _ : I => twistingSheaf k ι m) 0 =
      Fintype.card I * projectiveCohomologyDim k ι (twistingSheaf k ι m) 0 := by
  classical
  let α := projectiveConstants k ι
  let := moduleCohomologyModuleOfHom (ProjectiveSpace k ι) α
    (∐ fun _ : I => twistingSheaf k ι m) 0
  have : Module.Finite k ((moduleCohomologyFunctorOfHom (ProjectiveSpace k ι) α 0).obj
      (twistingSheaf k ι m)) := twistingCohomology_finite k ι n e m 0
  have : Module.Free k ((moduleCohomologyFunctorOfHom (ProjectiveSpace k ι) α 0).obj
      (twistingSheaf k ι m)) := twistingCohomology_free k ι n e m 0
  have h := (twistingCoproductCohomologyLinearEquiv k ι (fun _ : I => m) 0).finrank_eq
  unfold projectiveCohomologyDim
  rw [h]
  have hds := Module.finrank_directSum k (fun _ : I =>
    (moduleCohomologyFunctorOfHom (ProjectiveSpace k ι) α 0).obj (twistingSheaf k ι m))
  change Module.finrank k (DirectSum I fun _ => _) = _
  rw [hds, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rfl

/-- **The free module is ambient**: `∐_{i : I} O(0)` is coherent, `0`-regular, and
`h⁰(O(r) ⊗ O^I) ≤ |I| (r + 1)^{n+1}` for `r ≥ 0`. -/
theorem isMumfordAmbient_twistingCoproduct (n : ℕ) (e : ι ≃ Fin (n + 1)) (I : Type u)
    [Fintype I] :
    IsMumfordAmbient n (Fintype.card I) (∐ fun _ : I => twistingSheaf k ι 0) where
  coherent := by
    have : Finite ι := Finite.of_equiv _ e.symm
    exact twistingCoproduct_affineLocallyFiniteType k ι (fun _ : I => (0 : ℤ))
  regular q hq := by
    have : Finite ι := Finite.of_equiv _ e.symm
    by_cases hqn : q ≤ n
    · exact twistingTensorCoproductCohomology_subsingleton k ι n e ((0 : ℤ) - q)
        (fun _ : I => (0 : ℤ)) q (fun _ => by omega) (by omega)
    · have hc := twistingCoproduct_affineLocallyFiniteType k ι (fun _ : I => (0 : ℤ))
      have hT := twistingTensor_affineLocallyFiniteType k ι ((0 : ℤ) - q) _ hc
      have : ((moduleTensorLeftFunctor (ProjectiveSpace k ι)
          (twistingSheaf k ι ((0 : ℤ) - q))).obj
            (∐ fun _ : I => twistingSheaf k ι 0)).IsQuasicoherent :=
        quasicoherent_of_affineCharts _ (fun A j _ => (hT A j).1)
      exact projectiveCohomology_subsingleton_of_gt k ι n e _ q (by omega)
  dim_le r hr := by
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hr
    rw [projectiveCohomologyDim_congr k ι (twistingTensorCoproductIso k ι (m : ℤ)
      (fun _ : I => (0 : ℤ))) 0]
    simp only [add_zero]
    rw [projectiveCohomologyDim_twistingCoproduct_zero n e]
    have h := projectiveCohomologyDim_twistingSheaf_zero_le (k := k) n e m
    push_cast
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) (by positivity)

/-- **Mumford's bound for subsheaves of `O^p`, conditional on hyperplane sections**
(Nitsure, arXiv:math/0504590v1, Thm 2.3, p. 11): over a field with
`HasHyperplaneSections`, if `F` is a coherent submodule of `O^p = ∐_{i < p} O(0)` with
`χ(F(r)) = Σ_{i ≤ n} aᵢ C(r, i)` for all `r`, then `F` is `F_{p,n}(a)`-regular for the integer
polynomial `F_{p,n} = mumfordBound n p (n + 1)`, which depends only on `n` and `p`. -/
theorem isProjectiveRegular_mumfordBound_free_of_hasHyperplaneSections (n p : ℕ)
    (e : ι ≃ Fin (n + 1)) (hgen : HasHyperplaneSections k ι) {F : (ProjectiveSpace k ι).Modules}
    (j : F ⟶ ∐ fun _ : ULift.{u} (Fin p) => twistingSheaf k ι 0) [Mono j]
    (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) (a : Fin (n + 1) → ℤ)
    (hχ : ∀ r : ℤ, projectiveHilbertFunction k ι F r =
      ∑ i : Fin (n + 1), a i * Ring.choose r i) :
    IsProjectiveRegular k ι F (MvPolynomial.eval a (mumfordBound n p (n + 1))) := by
  have hG := isMumfordAmbient_twistingCoproduct (k := k) n e (ULift.{u} (Fin p))
  rw [Fintype.card_ulift, Fintype.card_fin] at hG
  exact isProjectiveRegular_mumfordBound_of_hasHyperplaneSections n p e hgen j hF hG a hχ

/-- **Mumford's bound for ideal sheaves, conditional on hyperplane sections** (Nitsure,
arXiv:math/0504590v1, Thm 2.3 with `p = 1`, the case used for Hilbert schemes): a coherent
submodule `F` of `O = O(0)` with `χ(F(r)) = Σ_{i ≤ n} aᵢ C(r, i)` is
`mumfordBound n 1 (n + 1)`-regular at `a`. -/
theorem isProjectiveRegular_mumfordBound_ideal_of_hasHyperplaneSections (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (hgen : HasHyperplaneSections k ι) {F : (ProjectiveSpace k ι).Modules}
    (j : F ⟶ twistingSheaf k ι 0) [Mono j]
    (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) (a : Fin (n + 1) → ℤ)
    (hχ : ∀ r : ℤ, projectiveHilbertFunction k ι F r =
      ∑ i : Fin (n + 1), a i * Ring.choose r i) :
    IsProjectiveRegular k ι F (MvPolynomial.eval a (mumfordBound n 1 (n + 1))) :=
  isProjectiveRegular_mumfordBound_free_of_hasHyperplaneSections n 1 e hgen
    (j ≫ (coproductUniqueIso fun _ : ULift.{u} (Fin 1) => twistingSheaf k ι 0).inv) hF a hχ

end AlgebraicGeometry.Scheme.Cohomology
