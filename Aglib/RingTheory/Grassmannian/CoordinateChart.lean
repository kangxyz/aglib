/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Grassmannian.ChartIntersection
public import Aglib.RingTheory.Grassmannian.Covering

/-!
# Unit-rescaled chart sections and rank-one coordinate charts

General facts about the charts of Mathlib's Grassmannian functor:

- `Module.Grassmannian.ofChartSection_eq_of_smul`: two chart sections, possibly for different
  charts, that differ by a unit scalar cut out the same point of the Grassmannian;
- `Module.Grassmannian.chartRing_algHom_ext`: algebra maps out of a chart ring are determined by
  their values on the coordinates `Φ_{a j}`;
- for rank-one quotients and coordinate tuples `I`: the coordinate `Φ_{0, I 0}` is `1` on the
  chart at `I` (`chartCoordinate_coordinateTuple_self`), and the transition determinant from the
  chart at `I` towards the chart at `J` is `Φ_{0, J 0}` (`chartTransitionDet_coordinateTuple`).

Their consumer is the comparison of the rank-one Grassmannian with projective space in
`Aglib.AlgebraicGeometry.Grassmannian.ProjectiveSpace`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open TensorProduct

universe u v w

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}
  {A : Type w} [CommRing A] [Algebra R A]

/-- Two chart sections, possibly for different charts, that differ by a unit scalar cut out the
same point of the Grassmannian. -/
theorem ofChartSection_eq_of_smul {x x' : Fin k → M} {φ φ' : M →ₗ[R] (Fin k → A)}
    (hφ : φ ∈ chartSections R A x) (hφ' : φ' ∈ chartSections R A x') (u : A) (hu : IsUnit u)
    (h : ∀ v, φ' v = u • φ v) :
    ofChartSection φ hφ = ofChartSection φ' hφ' := by
  have key : ∀ t, φ'.liftBaseChange A t = u • φ.liftBaseChange A t := by
    intro t
    induction t with
    | tmul a v => simp [LinearMap.liftBaseChange_tmul, h, smul_comm a u]
    | add t t' ht ht' => simp [ht, ht', smul_add]
  apply Module.Grassmannian.ext
  change LinearMap.ker (φ.liftBaseChange A) = LinearMap.ker (φ'.liftBaseChange A)
  ext t
  simp only [LinearMap.mem_ker, key, hu.smul_eq_zero]

/-- On the chart at a coordinate tuple `I`, the coordinate `Φ_{0, I 0}` is `1`. -/
theorem chartCoordinate_coordinateTuple_self {n : ℕ} (I : Fin 1 → Fin n) :
    chartCoordinate (coordinateTuple R I) 0 (I 0) = 1 := by
  have h := (Ideal.Quotient.eq_zero_iff_mem (I := chartIdeal R (coordinateTuple R I))).mpr
    (chartRelation_mem_chartIdeal (coordinateTuple R I) 0 0)
  simp only [chartRelation, coordinateTuple, Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_sub, map_one] at h
  exact sub_eq_zero.mp h

/-- For rank-one quotients, the transition determinant from the chart at `I` towards the chart at
`J` is the coordinate `Φ_{0, J 0}`. -/
theorem chartTransitionDet_coordinateTuple {n : ℕ} (I J : Fin 1 → Fin n) :
    chartTransitionDet (coordinateTuple R I) (coordinateTuple R J) =
      chartCoordinate (coordinateTuple R I) 0 (J 0) := by
  rw [chartTransitionDet, Matrix.det_unique]
  simp [chartTransitionMatrix, coordinateTuple, Pi.single_apply]

/-- Algebra maps out of a chart ring agree when they agree on the coordinates. -/
theorem chartRing_algHom_ext {n : ℕ} {x : Fin k → Fin n → R} {f g : ChartRing R x →ₐ[R] A}
    (h : ∀ a j, f (chartCoordinate x a j) = g (chartCoordinate x a j)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨a, j⟩
  exact h a j

end Module.Grassmannian
