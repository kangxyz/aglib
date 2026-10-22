/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.AwayAlgebra
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Native Segre chart ring map

The source is the actual degree-zero
homogeneous localization for the product-coordinate projective chart. The
target is the native tensor product of the two actual factor chart rings.
There is no finite-index, Noetherian, nonzero-ring, or Segre-existence premise.
-/

@[expose] public noncomputable section

open MvPolynomial
open scoped TensorProduct

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.Segre

variable (R : Type u) [CommRing R]

/-- Evaluate a native chart ring at coordinates normalized to one at its pivot. -/
def normalizedChartEval {α : Type u} (a : α)
    {B : Type v} [CommRing B] (c : R →+* B) (x : α → B) :
    coordinateRing R α a →+* B :=
  (eval₂Hom c (fun i : {i : α // i ≠ a} => x i.1)).comp
    (coordinateRingToPolynomial R α a)

@[simp]
theorem normalizedChartEval_coefficient {α : Type u} (a : α)
    {B : Type v} [CommRing B] (c : R →+* B) (x : α → B) (r : R) :
    normalizedChartEval R a c x (coordinateRingCoefficient R α a r) = c r := by
  simp [normalizedChartEval]

/-- The omitted pivot variable is sent to one, so the ratio formula requires
exactly the displayed normalization and no generation assumption. -/
theorem normalizedChartEval_ratio {α : Type u} (a : α)
    {B : Type v} [CommRing B] (c : R →+* B) (x : α → B)
    (hx : x a = 1) (i : α) :
    normalizedChartEval R a c x (coordinateRatio R α a i) = x i := by
  classical
  by_cases hi : i = a
  · subst i
    simp [hx]
  · change (eval₂Hom c (fun j : {j : α // j ≠ a} => x j.1))
      (coordinateRingToPolynomial R α a
        (coordinateRatio R α a (⟨i, hi⟩ : {j : α // j ≠ a}).1)) = _
    rw [coordinateRingToPolynomial_ratio, eval₂Hom_X']

variable {ι κ : Type u} (a : ι) (b : κ)

/-- The native coordinate algebra of the product of two standard affine charts. -/
abbrev chartTensor := coordinateRing R ι a ⊗[R] coordinateRing R κ b

/-- Product of the two normalized coordinate ratios, inside the actual tensor ring. -/
def chartValue (ij : ι × κ) : chartTensor R a b :=
  (Algebra.TensorProduct.includeLeft :
      coordinateRing R ι a →ₐ[R] chartTensor R a b)
      (coordinateRatio R ι a ij.1) *
    (Algebra.TensorProduct.includeRight :
      coordinateRing R κ b →ₐ[R] chartTensor R a b)
      (coordinateRatio R κ b ij.2)

@[simp]
theorem chartValue_pivot : chartValue R a b (a, b) = 1 := by
  simp only [chartValue, coordinateRatio_self, map_one, mul_one]

/-- On the chart `(a,b)`, Segre sends `z_(i,j)/z_(a,b)` to the product
`(x_i/x_a)(y_j/y_b)` in the native tensor product of factor chart rings. -/
def chartRingHom : coordinateRing R (ι × κ) (a, b) →+* chartTensor R a b :=
  normalizedChartEval R (a, b) (algebraMap R (chartTensor R a b)) (chartValue R a b)

@[simp]
theorem chartRingHom_coefficient (r : R) :
    chartRingHom R a b (coordinateRingCoefficient R (ι × κ) (a, b) r) =
      algebraMap R (chartTensor R a b) r := by
  simp [chartRingHom]

@[simp]
theorem chartRingHom_ratio (ij : ι × κ) :
    chartRingHom R a b (coordinateRatio R (ι × κ) (a, b) ij) =
      chartValue R a b ij :=
  normalizedChartEval_ratio R (a, b) _ _ (chartValue_pivot R a b) ij

/-- Each factor ratio occurs among the product ratios. Hence the actual Segre
chart ring map is surjective, over every commutative base ring. -/
theorem chartRingHom_surjective : Function.Surjective (chartRingHom R a b) := by
  let l : coordinateRing R ι a →+* chartTensor R a b :=
    Algebra.TensorProduct.includeLeftRingHom
  let r : coordinateRing R κ b →+* chartTensor R a b :=
    Algebra.TensorProduct.includeRight.toRingHom
  let liftL : MvPolynomial {i : ι // i ≠ a} R →+*
      coordinateRing R (ι × κ) (a, b) :=
    eval₂Hom (coordinateRingCoefficient R (ι × κ) (a, b))
      (fun i => coordinateRatio R (ι × κ) (a, b) (i.1, b))
  let liftR : MvPolynomial {j : κ // j ≠ b} R →+*
      coordinateRing R (ι × κ) (a, b) :=
    eval₂Hom (coordinateRingCoefficient R (ι × κ) (a, b))
      (fun j => coordinateRatio R (ι × κ) (a, b) (a, j.1))
  have hL : (chartRingHom R a b).comp liftL =
      l.comp (polynomialToCoordinateRing R ι a) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp only [RingHom.comp_apply, liftL, eval₂Hom_C,
        chartRingHom_coefficient, polynomialToCoordinateRing_C]
      exact (Algebra.TensorProduct.includeLeft.commutes x).symm
    · intro i
      simp [liftL, l, chartValue]
  have hR : (chartRingHom R a b).comp liftR =
      r.comp (polynomialToCoordinateRing R κ b) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp only [RingHom.comp_apply, liftR, eval₂Hom_C,
        chartRingHom_coefficient, polynomialToCoordinateRing_C]
      exact (Algebra.TensorProduct.includeRight.commutes x).symm
    · intro j
      simp [liftR, r, chartValue]
  have hl (x : coordinateRing R ι a) : ∃ z, chartRingHom R a b z = l x := by
    obtain ⟨p, hp⟩ := (coordinateRingEquivPolynomial R ι a).symm.surjective x
    refine ⟨liftL p, ?_⟩
    exact (RingHom.congr_fun hL p).trans (congrArg l hp)
  have hr (y : coordinateRing R κ b) : ∃ z, chartRingHom R a b z = r y := by
    obtain ⟨p, hp⟩ := (coordinateRingEquivPolynomial R κ b).symm.surjective y
    refine ⟨liftR p, ?_⟩
    exact (RingHom.congr_fun hR p).trans (congrArg r hp)
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    obtain ⟨x', hx⟩ := hl x
    obtain ⟨y', hy⟩ := hr y
    refine ⟨x' * y', ?_⟩
    rw [map_mul, hx, hy]
    simp [l, r]
  | add x y hx hy =>
    obtain ⟨x', hx⟩ := hx
    obtain ⟨y', hy⟩ := hy
    exact ⟨x' + y', by rw [map_add, hx, hy]⟩

end AlgebraicGeometry.ProjectiveSpace.Segre
