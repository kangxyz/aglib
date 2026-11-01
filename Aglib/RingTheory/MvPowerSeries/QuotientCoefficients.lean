/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPowerSeries.TruncIdeal
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Coefficients of the original variable-ideal quotients

Every finite-order quotient of the original power-series ring has its native
low-degree coefficients as finite free coordinates. The index includes order
zero without a positivity guard; no coefficient-ring completeness is assumed.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace MvPowerSeries

universe u v
variable {σ : Type u} [Finite σ] {A : Type v} [CommRing A]

local notation "I" => Ideal.span (Set.range (X : σ → MvPowerSeries σ A))

/-- Membership in an actual variable-ideal power is exactly low-coefficient vanishing. -/
theorem mem_span_X_pow_iff_coeff (n : ℕ) (f : MvPowerSeries σ A) :
    f ∈ I ^ n ↔ ∀ d : σ →₀ ℕ, d.degree < n → coeff d f = 0 := by
  classical
  have hmap : (MvPolynomial.idealOfVars σ A).map
      (algebraMap (MvPolynomial σ A) (MvPowerSeries σ A)) = I := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
    congr 1
    ext i
    simp [algebraMap_apply']
  constructor
  · intro hf
    have hle : I ^ n ≤ RingHom.ker (truncTotalAlgHom σ A n).toRingHom := by
      rw [← hmap, ← Ideal.map_pow, Ideal.map_le_iff_le_comap]
      intro p hp
      change truncTotalAlgHom σ A n (algebraMap (MvPolynomial σ A) _ p) = 0
      rw [(truncTotalAlgHom σ A n).commutes]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
    have hz := hle hf
    change Ideal.Quotient.mk (MvPolynomial.idealOfVars σ A ^ n) (f.truncTotal n) = 0 at hz
    have hc := (MvPolynomial.mem_pow_idealOfVars_iff' n _).mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    intro d hd
    simpa only [coeff_truncTotal _ hd] using hc d hd
  · intro hf
    have hz : f.truncTotal n = 0 := by
      ext d
      rw [coeff_truncTotal_eq_ite]
      split_ifs with hd
      · exact hf d hd
      · rfl
    simpa only [hz, MvPolynomial.coe_zero, sub_zero] using sub_truncTotal_mem_span_X_pow n f

/-- The finite type of original monomial exponents of degree below the order. -/
instance finite_lowDegreeExponents (n : ℕ) : Finite {d : σ →₀ ℕ // d.degree < n} :=
  (Finsupp.finite_of_degree_lt n).to_subtype

/-- The original quotient's coefficient map; no truncated ring is introduced. -/
def quotientCoefficients (n : ℕ) :
    (MvPowerSeries σ A ⧸ I ^ n) →ₗ[A] ({d : σ →₀ ℕ // d.degree < n} → A) :=
  ((I ^ n).restrictScalars A).liftQ (LinearMap.pi fun d => coeff d.val) (by
    intro f hf
    ext d
    exact (mem_span_X_pow_iff_coeff n f).mp hf d.val d.property)

@[simp] theorem quotientCoefficients_mk (n : ℕ) (f : MvPowerSeries σ A)
    (d : {d : σ →₀ ℕ // d.degree < n}) :
    quotientCoefficients n (Ideal.Quotient.mk (I ^ n) f) d = coeff d.val f := rfl

/-- Native quotient coefficients determine the original residue class uniquely. -/
theorem quotientCoefficients_injective (n : ℕ) :
    Function.Injective (quotientCoefficients (σ := σ) (A := A) n) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (mem_span_X_pow_iff_coeff n f).mpr
  intro d hd
  exact congrFun hq ⟨d, hd⟩

/-- Every finite low-coefficient vector is represented in the same power-series ring. -/
theorem quotientCoefficients_surjective (n : ℕ) :
    Function.Surjective (quotientCoefficients (σ := σ) (A := A) n) := by
  classical
  intro a
  let f : MvPowerSeries σ A := fun d => if h : d.degree < n then a ⟨d, h⟩ else 0
  refine ⟨Ideal.Quotient.mk (I ^ n) f, ?_⟩
  funext d
  calc
    _ = coeff d.val f := quotientCoefficients_mk n f d
    _ = a d := by
      change (if h : d.val.degree < n then a ⟨d.val, h⟩ else 0) = a d
      exact dite_eq_left d.property

/-- The coefficient-preserving finite free presentation of the actual quotient. -/
def quotientCoefficientsEquiv (n : ℕ) :
    (MvPowerSeries σ A ⧸ I ^ n) ≃ₗ[A] ({d : σ →₀ ℕ // d.degree < n} → A) :=
  LinearEquiv.ofBijective (quotientCoefficients n)
    ⟨quotientCoefficients_injective n, quotientCoefficients_surjective n⟩

@[simp] theorem quotientCoefficientsEquiv_mk (n : ℕ) (f : MvPowerSeries σ A)
    (d : {d : σ →₀ ℕ // d.degree < n}) :
    quotientCoefficientsEquiv n (Ideal.Quotient.mk (I ^ n) f) d = coeff d.val f := rfl

/-- The displayed basis consists of the original low-degree monomial classes. -/
def quotientMonomialBasis (n : ℕ) :
    Module.Basis {d : σ →₀ ℕ // d.degree < n} A (MvPowerSeries σ A ⧸ I ^ n) := by
  classical
  let := Fintype.ofFinite {d : σ →₀ ℕ // d.degree < n}
  exact (Pi.basisFun A _).map (quotientCoefficientsEquiv n).symm

@[simp] theorem quotientMonomialBasis_apply (n : ℕ)
    (d : {d : σ →₀ ℕ // d.degree < n}) :
    quotientMonomialBasis (A := A) n d = Ideal.Quotient.mk (I ^ n) (monomial d.val 1) := by
  classical
  apply (quotientCoefficientsEquiv n).injective
  ext e
  simp only [quotientMonomialBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    Pi.basisFun_apply, quotientCoefficientsEquiv_mk, coeff_monomial]
  by_cases h : e = d
  · subst e
    simp
  · have hv : e.val ≠ d.val := fun he => h (Subtype.ext he)
    simp [h, hv]

instance quotient_span_X_pow_free (n : ℕ) : Module.Free A (MvPowerSeries σ A ⧸ I ^ n) :=
  Module.Free.of_basis (quotientMonomialBasis n)

instance quotient_span_X_pow_finite (n : ℕ) : Module.Finite A (MvPowerSeries σ A ⧸ I ^ n) :=
  Module.Finite.of_basis (quotientMonomialBasis n)

/-- The entire reduction map is the original restriction of coefficient vectors. -/
theorem quotientCoefficients_reduction {m n : ℕ} (h : m ≤ n) :
    (quotientCoefficients (σ := σ) (A := A) m).comp
        (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right h : I ^ n ≤ I ^ m)).toLinearMap =
      (LinearMap.funLeft A A (fun d : {d : σ →₀ ℕ // d.degree < m} =>
        (⟨d.val, lt_of_lt_of_le d.property h⟩ : {d : σ →₀ ℕ // d.degree < n}))).comp
          (quotientCoefficients n) := by
  apply LinearMap.ext
  intro q
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  funext d
  change quotientCoefficients m (Ideal.Quotient.mk (I ^ m) f) d =
    quotientCoefficients n (Ideal.Quotient.mk (I ^ n) f)
      ⟨d.val, lt_of_lt_of_le d.property h⟩
  exact (quotientCoefficients_mk m f d).trans
    (quotientCoefficients_mk n f ⟨d.val, lt_of_lt_of_le d.property h⟩).symm

end MvPowerSeries
