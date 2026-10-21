/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationFiniteSystem
public import Aglib.RingTheory.MvPolynomial.FiniteSystemReindex

/-!
# The actual lower-dimensional induction step after preparation

A full finite-system approximation hypothesis in one fewer geometric variable
produces the parameter solution of the coupled remainder equations. The same
monic divisor is used for the determinant and its square for the equations.
The resulting point is corrected in the actual higher henselization. This
step still requires the displayed Weierstrass factorization; normalization is
not assumed to follow from mere high-order smallness.
-/

@[expose] public section

namespace PolynomialLocalHenselization

open MvPolynomial

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)

local notation "Aₙ" => PolynomialLocalHenselization R n
local notation "Bₙ" => PolynomialLocalRing.FormalSeries R n

/-- Full lower-dimensional approximation supplies the finite parameter tuple,
so the prepared selected system has an actual higher-dimensional root at
any requested precision. The induction hypothesis is not restricted to
square systems or systems with a nonzero Jacobian. -/
theorem exists_zero_of_prepared_selected_system
    (ih : ∀ (s t : ℕ) (E : Fin t → MvPolynomial (Fin s) Aₙ) (b : Fin s → Bₙ),
      (∀ i, eval₂ (toFormalSeries R n).toRingHom b (E i) = 0) →
      ∀ c : ℕ, ∃ a : Fin s → Aₙ,
        (∀ i, eval a (E i) = 0) ∧
        ∀ j, toFormalSeries R n (a j) - b j ∈ IsLocalRing.maximalIdeal Bₙ ^ c)
    {σ ν : Type*} [Fintype σ] [DecidableEq σ] [Finite ν] (selected : σ ↪ ν)
    (F : σ → MvPolynomial ν (Polynomial Aₙ)) (y : ν → PowerSeries Bₙ)
    (P : Polynomial Bₙ) (hP : P.IsDistinguishedAt (IsLocalRing.maximalIdeal Bₙ))
    (u : PowerSeries Bₙ) (hu : IsUnit u)
    (hF : ∀ i, eval₂Hom
      (Polynomial.coeToPowerSeries.ringHom.comp
        (Polynomial.mapRingHom (toFormalSeries R n).toRingHom)) y (F i) = 0)
    (hg : eval₂Hom
      (Polynomial.coeToPowerSeries.ringHom.comp
        (Polynomial.mapRingHom (toFormalSeries R n).toRingHom)) y
      (Matrix.det (Matrix.of fun i j => pderiv (selected j) (F i))) =
        (P : PowerSeries Bₙ) * u) (c : ℕ) :
    ∃ y' : ν → PolynomialLocalHenselization R (n + 1),
      (∀ i, eval y' (MvPolynomial.map (polynomialEvaluation R n).toRingHom (F i)) = 0) ∧
      ∀ i, iteratedFormalMap R n (y' i) - y i ∈
        IsLocalRing.maximalIdeal (PowerSeries Bₙ) ^ c := by
  let c' := max c (P.natDegree + 1)
  have hc' : P.natDegree < c' :=
    lt_of_lt_of_le (Nat.lt_succ_self P.natDegree) (le_max_right _ _)
  obtain ⟨z, b, hg₀, hF₀, hreduce⟩ :=
    exists_finite_system_for_selected_correction R n selected F y P hP u hu c' hc' hF hg
  let x₀ := Sum.elim (fun j : Fin P.natDegree => P.coeff j) b
  let g := Matrix.det (Matrix.of fun i j => pderiv (selected j) (F i))
  let E : (Fin P.natDegree ⊕ (σ × Fin (2 * P.natDegree))) →
      MvPolynomial (Fin P.natDegree ⊕ (ν × Fin (2 * P.natDegree))) Aₙ :=
    Sum.elim (coupledDivisibilityEquation P.natDegree z g)
      (fun q => coupledSquareDivisibilityEquation P.natDegree z (F q.1) q.2)
  have hE : ∀ i, eval₂ ((toFormalSeries R n).toRingHom.comp (RingHom.id Aₙ))
      x₀ (E i) = 0 := by
    intro i
    cases i with
    | inl j => exact hg₀ j
    | inr q => exact hF₀ q
  obtain ⟨t, ht, hclose⟩ := MvPolynomial.exists_finite_solution_of_fin_solver
    (RingHom.id Aₙ) (toFormalSeries R n).toRingHom (IsLocalRing.maximalIdeal Bₙ)
    (fun s t E b hE c => ih s t E b (by simpa only [RingHom.comp_id] using hE) c)
    E x₀ hE c'
  obtain ⟨y', hy', hprecision⟩ := hreduce t hclose
    ⟨(fun j => ht (Sum.inl j)), fun q => ht (Sum.inr q)⟩
  refine ⟨y', hy', fun i => ?_⟩
  exact Ideal.pow_le_pow_right (le_max_left c (P.natDegree + 1)) (hprecision i)

end PolynomialLocalHenselization
