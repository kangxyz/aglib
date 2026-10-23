/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Grassmannian.CoordinateChart
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Coordinate charts of the Grassmannian are affine spaces

Let `I : Fin k → Fin n` and let `x = coordinateTuple R I` be the coordinate tuple `x b = e_{I b}`.
The relations of the chart ring `ChartRing R x = R[Φ_{aj}] ⧸ (Φ X - 1)` say `Φ_{a, I b} = δ_{ab}`
(`chartRelation_coordinateTuple`, `chartCoordinate_coordinateTuple`).

* If `I` is injective, the remaining coordinates are free: `chartRingEquivMvPolynomial R hI` is an
  `R`-algebra isomorphism from `ChartRing R x` to the polynomial ring over `R` in the coordinates
  `Φ_{aj}` with `j ∉ range I` (`ChartFreeIndex I`).
* If `I` is not injective, the chart ring is the zero ring (`subsingleton_chartRing`).

Hence every coordinate chart ring is smooth over `R` (`smooth_chartRing`), in particular flat
(`flat_chartRing`).

Sources: Stacks, Tag 089T (Lemma 27.22.1, proof: the subfunctors `F_i` are affine spaces
`A^{k(n-k)}`); Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §1,
p. 8 (the charts `U^I = Spec Z[X^I]`, and `Grass(r, d) → Spec Z` is smooth of relative dimension
`d(r - d)`). Here `k` is the rank of the quotient.
-/

@[expose] public section

noncomputable section

open MvPolynomial

universe u

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {k n : ℕ}

/-- The relations of the chart at a coordinate tuple: the `(a, b)` entry of `Φ X - 1` is
`Φ_{a, I b} - δ_{ab}`. -/
theorem chartRelation_coordinateTuple (I : Fin k → Fin n) (a b : Fin k) :
    chartRelation R (coordinateTuple R I) a b = X (a, I b) - if a = b then 1 else 0 := by
  simp only [chartRelation, coordinateTuple, Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- On the chart at a coordinate tuple `I`, the coordinate `Φ_{a, I b}` is `δ_{ab}`. -/
theorem chartCoordinate_coordinateTuple (I : Fin k → Fin n) (a b : Fin k) :
    chartCoordinate (coordinateTuple R I) a (I b) = if a = b then 1 else 0 := by
  have h := (Ideal.Quotient.eq_zero_iff_mem (I := chartIdeal R (coordinateTuple R I))).mpr
    (chartRelation_mem_chartIdeal (coordinateTuple R I) a b)
  rw [chartRelation_coordinateTuple, map_sub, sub_eq_zero] at h
  rw [chartCoordinate, h]
  split_ifs <;> simp

/-- The free coordinates `Φ_{aj}`, `j ∉ range I`, of the chart at a coordinate tuple `I`. -/
abbrev ChartFreeIndex (I : Fin k → Fin n) : Type :=
  {aj : Fin k × Fin n // aj.2 ∉ Set.range I}

variable (R) in
/-- The value of the coordinate `Φ_{aj}` in the polynomial ring in the free coordinates:
`δ_{ab}` if `j = I b`, and the variable `X_{aj}` if `j ∉ range I`. -/
def chartFreeValue (I : Fin k → Fin n) (aj : Fin k × Fin n) :
    MvPolynomial (ChartFreeIndex I) R :=
  if h : ∃ b, I b = aj.2 then (if I aj.1 = aj.2 then 1 else 0) else X ⟨aj, h⟩

theorem chartFreeValue_apply_range {I : Fin k → Fin n} (hI : Function.Injective I) (a b : Fin k) :
    chartFreeValue R I (a, I b) = if a = b then 1 else 0 := by
  rw [chartFreeValue, dite_eq_left ⟨b, rfl⟩]
  simp only [hI.eq_iff]

theorem chartFreeValue_of_notMem (I : Fin k → Fin n) (aj : Fin k × Fin n)
    (h : aj.2 ∉ Set.range I) : chartFreeValue R I aj = X ⟨aj, h⟩ :=
  dite_eq_right h

theorem aeval_chartFreeValue_eq_zero {I : Fin k → Fin n} (hI : Function.Injective I) :
    ∀ p ∈ chartIdeal R (coordinateTuple R I), aeval (chartFreeValue R I) p = 0 := by
  have hle : chartIdeal R (coordinateTuple R I) ≤
      RingHom.ker (aeval (R := R) (chartFreeValue R I)) := by
    rw [chartIdeal, Ideal.span_le]
    rintro _ ⟨⟨a, b⟩, rfl⟩
    change aeval (chartFreeValue R I) (chartRelation R (coordinateTuple R I) a b) = 0
    rw [chartRelation_coordinateTuple, map_sub, aeval_X,
      chartFreeValue_apply_range hI]
    split_ifs <;> simp
  exact fun p hp => hle hp

variable (R) in
/-- The algebra map from the chart ring at an injective coordinate tuple to the polynomial ring
in the free coordinates. -/
def chartRingToMvPolynomial {I : Fin k → Fin n} (hI : Function.Injective I) :
    ChartRing R (coordinateTuple R I) →ₐ[R] MvPolynomial (ChartFreeIndex I) R :=
  Ideal.Quotient.liftₐ (chartIdeal R (coordinateTuple R I)) (aeval (chartFreeValue R I))
    (aeval_chartFreeValue_eq_zero hI)

theorem chartRingToMvPolynomial_coordinate {I : Fin k → Fin n} (hI : Function.Injective I)
    (a : Fin k) (j : Fin n) :
    chartRingToMvPolynomial R hI (chartCoordinate (coordinateTuple R I) a j) =
      chartFreeValue R I (a, j) := by
  have h := AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp (chartIdeal R (coordinateTuple R I))
    (aeval (chartFreeValue R I)) (aeval_chartFreeValue_eq_zero hI)) (X (a, j))
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, aeval_X] at h
  exact h

variable (R) in
/-- The algebra map from the polynomial ring in the free coordinates to the chart ring at a
coordinate tuple, `X_{aj} ↦ Φ_{aj}`. -/
def mvPolynomialToChartRing (I : Fin k → Fin n) :
    MvPolynomial (ChartFreeIndex I) R →ₐ[R] ChartRing R (coordinateTuple R I) :=
  aeval fun p => chartCoordinate (coordinateTuple R I) p.1.1 p.1.2

variable (R) in
/-- **The chart at an injective coordinate tuple is an affine space**: its coordinate ring is the
polynomial ring over `R` in the `k (n - k)` free coordinates `Φ_{aj}`, `j ∉ range I`.
Stacks, Tag 089T (proof of Lemma 27.22.1); Nitsure, arXiv:math/0504590v1, §1, p. 8. -/
def chartRingEquivMvPolynomial {I : Fin k → Fin n} (hI : Function.Injective I) :
    ChartRing R (coordinateTuple R I) ≃ₐ[R] MvPolynomial (ChartFreeIndex I) R :=
  AlgEquiv.ofAlgHom (chartRingToMvPolynomial R hI) (mvPolynomialToChartRing R I)
    (MvPolynomial.algHom_ext fun p => by
      rw [AlgHom.comp_apply, AlgHom.id_apply, mvPolynomialToChartRing, aeval_X,
        chartRingToMvPolynomial_coordinate, chartFreeValue_of_notMem I p.1 p.2])
    (chartRing_algHom_ext fun a j => by
      rw [AlgHom.comp_apply, AlgHom.id_apply, chartRingToMvPolynomial_coordinate]
      by_cases hj : j ∈ Set.range I
      · obtain ⟨b, rfl⟩ := hj
        rw [chartFreeValue_apply_range hI, chartCoordinate_coordinateTuple]
        split_ifs <;> simp
      · rw [chartFreeValue_of_notMem I (a, j) hj, mvPolynomialToChartRing, aeval_X])

/-- At a non-injective coordinate tuple the chart ring is the zero ring: if `I a = I b` with
`a ≠ b`, the relations give `1 = Φ_{a, I a} = Φ_{a, I b} = 0`. -/
theorem subsingleton_chartRing {I : Fin k → Fin n} (hI : ¬ Function.Injective I) :
    Subsingleton (ChartRing R (coordinateTuple R I)) := by
  simp only [Function.Injective, not_forall] at hI
  obtain ⟨a, b, hab, hne⟩ := hI
  apply subsingleton_of_zero_eq_one
  have h1 := chartCoordinate_coordinateTuple (R := R) I a a
  have h0 := chartCoordinate_coordinateTuple (R := R) I a b
  rw [ite_eq_left rfl] at h1
  rw [ite_eq_right hne, ← hab, h1] at h0
  exact h0.symm

variable (R) in
/-- **Every coordinate chart ring of the Grassmannian is smooth over `R`**: a polynomial ring in
finitely many variables, or the zero ring. -/
theorem smooth_chartRing (I : Fin k → Fin n) :
    Algebra.Smooth R (ChartRing R (coordinateTuple R I)) := by
  by_cases hI : Function.Injective I
  · exact Algebra.Smooth.of_equiv (chartRingEquivMvPolynomial R hI).symm
  · have := subsingleton_chartRing (R := R) hI
    infer_instance

variable (R) in
/-- Every coordinate chart ring of the Grassmannian is flat over `R`. -/
theorem flat_chartRing (I : Fin k → Fin n) :
    Module.Flat R (ChartRing R (coordinateTuple R I)) :=
  have := smooth_chartRing R I
  inferInstance

end Module.Grassmannian
