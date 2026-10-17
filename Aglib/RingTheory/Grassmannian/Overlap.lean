/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Grassmannian.Chart
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Overlaps of Grassmannian charts

Let `φ : M → A^k` be the linear section of a point of the chart at `x`. The point lies in the
chart at another tuple `y` exactly when the transition matrix `(φ (y b) a)_{a b}` is invertible.
For coordinate tuples this is Nitsure's description of `U^I_J ⊆ U^I` as the locus where the
minor `P^I_J = det (X^I_J)` is invertible (Nitsure, arXiv:math/0504590v1, §1,
"Construction of Grassmannian", p. 8); in general it identifies the intersection of two charts
with a basic open subset of either chart.

## Main results

- `Module.Grassmannian.transitionMatrix`: the matrix `(φ (y b) a)_{a b}`.
- `Module.Grassmannian.ofChartSection_mem_chart_iff`: the point cut out by `φ` lies in the chart
  at `y` if and only if `det (transitionMatrix φ y)` is a unit.
- `Module.Grassmannian.mem_chart_iff_isUnit_det`: the same criterion for a point of the chart at
  `x`, in terms of its linear section.
-/

@[expose] public section

noncomputable section

universe u v w

open TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}
variable {A : Type w} [CommRing A] [Algebra R A]

/-- The transition matrix `(φ (y b) a)_{a b}` of a linear map `φ : M → A^k` at a tuple `y`. -/
def transitionMatrix (φ : M →ₗ[R] (Fin k → A)) (y : Fin k → M) : Matrix (Fin k) (Fin k) A :=
  Matrix.of fun a b ↦ φ (y b) a

@[simp]
theorem transitionMatrix_apply (φ : M →ₗ[R] (Fin k → A)) (y : Fin k → M) (a b : Fin k) :
    transitionMatrix φ y a b = φ (y b) a :=
  rfl

/-- Under the identification of the quotient with `A^k`, the chart map at `y` of the point cut
out by `φ` is multiplication by the transition matrix. -/
theorem ofChartSectionQuotientEquiv_comp_chartMap_eq_mulVecLin {x : Fin k → M}
    (φ : M →ₗ[R] (Fin k → A)) (hφ : φ ∈ chartSections R A x) (y : Fin k → M) :
    (ofChartSectionQuotientEquiv φ hφ).toLinearMap ∘ₗ
        chartMap (baseChangeTuple A y) (ofChartSection φ hφ).toSubmodule =
      (transitionMatrix φ y).mulVecLin := by
  refine LinearMap.pi_ext' fun b ↦ LinearMap.ext_ring ?_
  ext a
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The point cut out by a linear section `φ` lies in the chart at `y` if and only if the
transition matrix of `φ` at `y` has a unit determinant. -/
theorem ofChartSection_mem_chart_iff {x : Fin k → M} (φ : M →ₗ[R] (Fin k → A))
    (hφ : φ ∈ chartSections R A x) (y : Fin k → M) :
    ofChartSection φ hφ ∈ chart A (baseChangeTuple A y) ↔
      IsUnit (transitionMatrix φ y).det := by
  have h := ofChartSectionQuotientEquiv_comp_chartMap_eq_mulVecLin φ hφ y
  have h' : chartMap (baseChangeTuple A y) (ofChartSection φ hφ).toSubmodule =
      (ofChartSectionQuotientEquiv φ hφ).symm.toLinearMap ∘ₗ
        (transitionMatrix φ y).mulVecLin := by
    rw [← h]
    ext c
    simp
  rw [mem_chart_iff, h', ← Matrix.isUnit_iff_isUnit_det, LinearMap.coe_comp,
    Matrix.coe_mulVecLin]
  constructor
  · intro hb
    refine Matrix.mulVec_surjective_iff_isUnit.mp fun v ↦ ?_
    obtain ⟨c, hc⟩ := hb.2 ((ofChartSectionQuotientEquiv φ hφ).symm v)
    exact ⟨c, (ofChartSectionQuotientEquiv φ hφ).symm.injective hc⟩
  · intro hu
    exact (ofChartSectionQuotientEquiv φ hφ).symm.bijective.comp
      ⟨Matrix.mulVec_injective_of_isUnit hu, Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩

/-- A point of the chart at `x` lies in the chart at `y` if and only if the transition matrix
of its linear section at `y` has a unit determinant. -/
theorem mem_chart_iff_isUnit_det {x : Fin k → M} {N : G(k, A ⊗[R] M; A)}
    (hN : N ∈ chart A (baseChangeTuple A x)) (y : Fin k → M) :
    N ∈ chart A (baseChangeTuple A y) ↔ IsUnit (transitionMatrix (toChartSection hN) y).det := by
  conv_lhs => rw [← ofChartSection_toChartSection hN]
  exact ofChartSection_mem_chart_iff _ _ y

end Module.Grassmannian
