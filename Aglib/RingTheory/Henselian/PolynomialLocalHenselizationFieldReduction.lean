/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.FieldEvaluationComponent
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationFieldBase
public import Aglib.RingTheory.MvPolynomial.FormalPrimeReduction

/-!
# Selected-equation reduction in the actual polynomial henselization over a field

The original source and formal maps are used throughout. The generic component
is formally smooth by the arbitrary-field series separability theorem, not by
an additional hypothesis. Solving the selected equations is still a separate
step; the induction hypothesis used in that step must cover all finite systems
with arbitrary coefficients in the lower-dimensional henselization.
-/

@[expose] public section

noncomputable section

namespace PolynomialLocalHenselization

variable (k : Type*) [Field k] (n : ℕ)

local instance {A C σ : Type*} [CommRing A] [CommRing C] [IsDomain C]
    (f : A →+* C) (y : σ → C) :
    (RingHom.ker (MvPolynomial.eval₂Hom f y)).IsPrime := RingHom.ker_isPrime _

/-- Polynomial coefficients act through localization and the canonical henselization map. -/
local instance polynomialHenselizationAlgebra :
    Algebra (MvPolynomial (Fin n) k) (PolynomialLocalHenselization k n) :=
  ((algebraMap (PolynomialLocalRing k n) (PolynomialLocalHenselization k n)).comp
    (algebraMap (MvPolynomial (Fin n) k) (PolynomialLocalRing k n))).toAlgebra

local instance : IsScalarTower (MvPolynomial (Fin n) k) (PolynomialLocalRing k n)
    (PolynomialLocalHenselization k n) := IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The original henselized formal map restricts to the native polynomial
coefficient map, including its completed coefficient action. -/
theorem toFormalSeries_comp_polynomial_algebraMap :
    (toFormalSeries k n).toRingHom.comp
      (algebraMap (MvPolynomial (Fin n) k) (PolynomialLocalHenselization k n)) =
      algebraMap (MvPolynomial (Fin n) k) (PolynomialLocalRing.FormalSeries k n) := by
  let P := MvPolynomial (Fin n) k
  let L := PolynomialLocalRing k n
  let H := PolynomialLocalHenselization k n
  let C := PolynomialLocalRing.FormalSeries k n
  have hp : PolynomialLocalRing.polynomialToFormalSeries k n =
      MvPolynomial.coeToMvPowerSeries.algHom
        (AdicCompletion (IsLocalRing.maximalIdeal k) k) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [PolynomialLocalRing.polynomialToFormalSeries, MvPolynomial.aeval_X,
      MvPolynomial.coeToMvPowerSeries.algHom_apply, MvPolynomial.coe_X, MvPowerSeries.map_X]
  apply RingHom.ext
  intro p
  change toFormalSeries k n (algebraMap P H p) = algebraMap P C p
  rw [IsScalarTower.algebraMap_apply P L H]
  have h := AlgHom.congr_fun (toFormalSeries_comp_of k n) (algebraMap P L p)
  change toFormalSeries k n (algebraMap L H (algebraMap P L p)) =
    PolynomialLocalRing.toFormalSeries k n (algebraMap P L p) at h
  rw [h, PolynomialLocalRing.toFormalSeries_algebraMap]
  exact AlgHom.congr_fun hp p

/-- At an arbitrary formal point over a field, select actual relations and
variable columns with nonzero determinant; sufficiently close source solutions
of those relations solve every original equation. No solution-existence or
square-system assumption is hidden in this reduction. -/
theorem exists_selected_system_at_formal_point {σ ι : Type*} [Finite σ]
    (F : ι → MvPolynomial σ (MvPolynomial (Fin n) k))
    (y : σ → PolynomialLocalRing.FormalSeries k n)
    (hy : ∀ i, MvPolynomial.eval₂
      (algebraMap (MvPolynomial (Fin n) k) (PolynomialLocalRing.FormalSeries k n))
        y (F i) = 0) (c : ℕ) :
    ∃ (r : ℕ) (G : Fin r → MvPolynomial σ (MvPolynomial (Fin n) k))
      (cols : Fin r ↪ σ) (N : ℕ),
      c ≤ N ∧
      (∀ j, MvPolynomial.eval₂
        (algebraMap (MvPolynomial (Fin n) k) (PolynomialLocalRing.FormalSeries k n))
          y (G j) = 0) ∧
      MvPolynomial.eval₂
        (algebraMap (MvPolynomial (Fin n) k) (PolynomialLocalRing.FormalSeries k n)) y
        (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv (cols j) (G i))) ≠ 0 ∧
      ∀ x : σ → PolynomialLocalHenselization k n,
        (∀ j, toFormalSeries k n (x j) - y j ∈
          IsLocalRing.maximalIdeal (PolynomialLocalRing.FormalSeries k n) ^ N) →
        (∀ j, MvPolynomial.eval₂
          (algebraMap (MvPolynomial (Fin n) k) (PolynomialLocalHenselization k n))
            x (G j) = 0) →
        ∀ i, MvPolynomial.eval₂
          (algebraMap (MvPolynomial (Fin n) k) (PolynomialLocalHenselization k n))
            x (F i) = 0 := by
  let P := MvPolynomial (Fin n) k
  let H := PolynomialLocalHenselization k n
  let C := PolynomialLocalRing.FormalSeries k n
  let : IsDomain (MvPowerSeries (Fin n) k) := NoZeroDivisors.to_isDomain _
  let : IsDomain C := MulEquiv.isDomain (MvPowerSeries (Fin n) k)
    (PolynomialLocalRing.formalSeriesFieldEquiv k n).toMulEquiv
  let : IsAdicComplete (IsLocalRing.maximalIdeal C) C :=
    PolynomialLocalRing.formalSeries_isAdicComplete k n
  let φ := algebraMap P H
  let τ := (toFormalSeries k n).toRingHom
  have hcomp : τ.comp φ = algebraMap P C := toFormalSeries_comp_polynomial_algebraMap k n
  let : Algebra.FormallySmooth P
      (RingHom.ker (MvPolynomial.eval₂Hom (τ.comp φ) y)).ResidueField := by
    rw [hcomp]
    exact PolynomialLocalRing.formallySmooth_evaluation_residueField k n y
  have hy' : ∀ i, MvPolynomial.eval₂ (τ.comp φ) y (F i) = 0 := by
    simpa only [hcomp] using hy
  obtain ⟨r, G, cols, N, hN, hG, hdet, hrecover⟩ :=
    MvPolynomial.exists_selected_system_at_formal_prime (IsLocalRing.maximalIdeal C)
      φ τ (toFormalSeries_injective k n) F y hy' c
  refine ⟨r, G, cols, N, hN, ?_, ?_, ?_⟩
  · simpa only [hcomp] using hG
  · simpa only [hcomp] using hdet
  · intro x hx hxG
    exact hrecover x hx hxG

end PolynomialLocalHenselization
