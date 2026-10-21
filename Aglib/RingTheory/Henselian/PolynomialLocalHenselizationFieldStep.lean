/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationSelectedStep
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationFieldReduction

/-!
# The polynomial-coefficient induction step over an arbitrary field

The actual coefficient completion has zero maximal ideal, so a nonzero
selected determinant satisfies the residue condition for preparation. Generic
prime reduction, the lower-dimensional full induction hypothesis, and recovery
of the original equations then give the polynomial-coefficient solver in the
higher dimension. No perfection or characteristic restriction is imposed.
-/

@[expose] public section

noncomputable section

namespace PolynomialLocalHenselization

open MvPolynomial IsLocalRing

variable (k : Type*) [Field k] (n : ℕ)

local notation "Aₙ" => PolynomialLocalHenselization k n
local notation "Bₙ" => PolynomialLocalRing.FormalSeries k n

/-- The native polynomial algebra action agrees with the original polynomial formal map. -/
theorem polynomialToFormalSeries_eq_algebraMap (d : ℕ) :
    (PolynomialLocalRing.polynomialToFormalSeries k d).toRingHom =
      algebraMap (MvPolynomial (Fin d) k) (PolynomialLocalRing.FormalSeries k d) := by
  apply RingHom.ext
  intro p
  change PolynomialLocalRing.polynomialToFormalSeries k d p = _
  exact (toFormalSeries_polynomialToHenselization k d p).symm.trans
    (RingHom.congr_fun (toFormalSeries_comp_polynomial_algebraMap k d) p)

/-- Over a field, ordinary nonvanishing suffices for the selected-system step. -/
theorem exists_zero_of_selected_polynomial_system
    (ih : ∀ (s t : ℕ) (E : Fin t → MvPolynomial (Fin s) Aₙ) (b : Fin s → Bₙ),
      (∀ i, eval₂ (toFormalSeries k n).toRingHom b (E i) = 0) →
      ∀ c : ℕ, ∃ a : Fin s → Aₙ,
        (∀ i, eval a (E i) = 0) ∧
        ∀ j, toFormalSeries k n (a j) - b j ∈ maximalIdeal Bₙ ^ c)
    {σ ν : Type*} [Fintype σ] [DecidableEq σ] [Finite ν] (selected : σ ↪ ν)
    (F : σ → MvPolynomial ν (MvPolynomial (Fin (n + 1)) k))
    (y : ν → PolynomialLocalRing.FormalSeries k (n + 1))
    (hF : ∀ i, eval₂
      (algebraMap (MvPolynomial (Fin (n + 1)) k) (PolynomialLocalRing.FormalSeries k (n + 1)))
      y (F i) = 0)
    (hg : eval₂
      (algebraMap (MvPolynomial (Fin (n + 1)) k) (PolynomialLocalRing.FormalSeries k (n + 1)))
      y (Matrix.det (Matrix.of fun i j => pderiv (selected j) (F i))) ≠ 0) (c : ℕ) :
    ∃ x : ν → PolynomialLocalHenselization k (n + 1),
      (∀ i, eval₂ (polynomialToHenselization k (n + 1)).toRingHom x (F i) = 0) ∧
      ∀ j, toFormalSeries k (n + 1) (x j) - y j ∈
        maximalIdeal (PolynomialLocalRing.FormalSeries k (n + 1)) ^ c := by
  let Rhat := AdicCompletion (maximalIdeal k) k
  let : IsAdicComplete (maximalIdeal k) k := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  let ec := AdicCompletion.ofAlgEquiv (maximalIdeal k)
  have hmax : maximalIdeal Rhat = ⊥ := by
    apply (Ideal.map_eq_bot_iff_of_injective ec.symm.injective).mp
    change (maximalIdeal Rhat).map ec.symm.toRingEquiv = ⊥
    rw [IsLocalRing.map_ringEquiv_maximalIdeal, IsLocalRing.maximalIdeal_eq_bot]
  have hres : Function.Injective (residue Rhat) := by
    apply (RingHom.injective_iff_ker_eq_bot _).mpr
    rw [IsLocalRing.ker_residue, hmax]
  have hnonzero : MvPowerSeries.map (residue Rhat)
      (eval₂ (PolynomialLocalRing.polynomialToFormalSeries k (n + 1)).toRingHom y
        (Matrix.det (Matrix.of fun i j => pderiv (selected j) (F i)))) ≠ 0 := by
    rw [polynomialToFormalSeries_eq_algebraMap]
    intro hz
    apply hg
    apply MvPowerSeries.ext
    intro d
    apply hres
    have h := congrArg (MvPowerSeries.coeff d) hz
    simpa only [MvPowerSeries.coeff_map, map_zero] using h
  apply exists_zero_of_selected_polynomial_system_of_residue_ne_zero k n ih selected
    F y ?_ hnonzero c
  simpa only [polynomialToFormalSeries_eq_algebraMap] using hF

/-- Full approximation one dimension lower solves every polynomial-coefficient
system in the actual higher henselization, after generic selection and exact
recovery of all original equations. -/
theorem exists_polynomial_coefficient_solution_of_lower_approximation
    (ih : ∀ (s t : ℕ) (E : Fin t → MvPolynomial (Fin s) Aₙ) (b : Fin s → Bₙ),
      (∀ i, eval₂ (toFormalSeries k n).toRingHom b (E i) = 0) →
      ∀ c : ℕ, ∃ a : Fin s → Aₙ,
        (∀ i, eval a (E i) = 0) ∧
        ∀ j, toFormalSeries k n (a j) - b j ∈ maximalIdeal Bₙ ^ c)
    {σ ι : Type*} [Finite σ]
    (F : ι → MvPolynomial σ (MvPolynomial (Fin (n + 1)) k))
    (y : σ → PolynomialLocalRing.FormalSeries k (n + 1))
    (hy : ∀ i, eval₂
      (algebraMap (MvPolynomial (Fin (n + 1)) k) (PolynomialLocalRing.FormalSeries k (n + 1)))
      y (F i) = 0) (c : ℕ) :
    ∃ x : σ → PolynomialLocalHenselization k (n + 1),
      (∀ i, eval₂ (polynomialToHenselization k (n + 1)).toRingHom x (F i) = 0) ∧
      ∀ j, toFormalSeries k (n + 1) (x j) - y j ∈
        maximalIdeal (PolynomialLocalRing.FormalSeries k (n + 1)) ^ c := by
  obtain ⟨r, G, cols, N, hc, hG, hdet, hrecover⟩ :=
    exists_selected_system_at_formal_point k (n + 1) F y hy c
  obtain ⟨x, hx, hclose⟩ :=
    exists_zero_of_selected_polynomial_system k n ih cols G y hG hdet N
  refine ⟨x, ?_, fun j => Ideal.pow_le_pow_right hc (hclose j)⟩
  exact hrecover x hclose hx

end PolynomialLocalHenselization
