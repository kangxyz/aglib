/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Grassmannian.ProjectiveSpace.Charts
public import Aglib.AlgebraicGeometry.ProjectiveSpace.GlobalGeneration

/-!
# The universal quotient of projective space in the standard frames

Aglib's twisting sheaf `twistingSheaf R ι 1 = O(1)` receives the quotient map
`coordinatePowerGeneratingMap R ι 1 : O^ι ↠ O(1)` given by the coordinate sections, an
epimorphism sending the free generator `e_k` to `X_k`. On the standard chart `D₊(Xᵢ)`, in the
frame of `O(1)` given by `Xᵢ`, the image of `e_k` has the coefficient `X_k / X_i`. The point of
the Grassmannian of rank-one quotients classified by `D₊(Xᵢ) ⊂ P` is cut out by the chart section
`chartRatioSection e i` (`representableEquiv_chartOver`), and the components of this section,
transported along Mathlib's identification `B_i ≅ Γ(D₊(Xᵢ), O)`, are these frame coefficients
(`awayToSection_chartRatioSection`). On the overlap `D₊(Xᵢ Xₗ)` the chart sections at `i` and
`l` differ by the transition unit `Xᵢ / Xₗ` of the twisting sheaves
(`overlapRight_chartRatioSection`), which is the unit of the Grassmannian overlap comparison
(`overlapRight_ratio_eq_coordinateTransitionUnit`).

No second twisting sheaf is constructed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] {ι : Type u}

/-- The coordinate `X_k`, as a polynomial of degree one, is `X_k / X_i` in the standard frame on
`D₊(Xᵢ)`. -/
theorem homogeneousChartFraction_coordinatePower_one (k i : ι) :
    homogeneousChartFraction R ι 1 (coordinatePower R ι 1 k) i = coordinateRatio R ι i k := by
  apply HomogeneousLocalization.val_injective
  simp [homogeneousChartFraction, coordinatePower, coordinateRatio]

variable {m : ℕ} (e : ι ≃ Fin m)

/-- **The chart quotients of the universal point are the frame coefficients of the coordinate
sections.** On `D₊(Xᵢ)`, the `j`-th component of the chart section `chartRatioSection e i`,
transported to `Γ(D₊(Xᵢ), O)` by Mathlib's canonical map, is the coefficient in the frame `Xᵢ` of
the image of the free generator `e_{e⁻¹ j}` under the quotient map
`coordinatePowerGeneratingMap R ι 1 : O^ι ↠ O(1)` given by the coordinate sections. -/
theorem awayToSection_chartRatioSection (i : ι) (j : Fin m) :
    Proj.awayToSection (homogeneousSubmodule ι R) (X i)
        (chartRatioSection R e i (Pi.single j 1) 0) =
      twistingSectionsEquiv R ι ((1 : ℕ) : ℤ) i le_rfl
        ((coordinatePowerGeneratingMap R ι 1).val.app (op (coordinateOpen R ι i))
          ((SheafOfModules.freeSection (R := (ProjectiveSpace R ι).ringCatSheaf)
            (e.symm j)).val (op (coordinateOpen R ι i)))) := by
  rw [coordinatePowerGeneratingMap_freeSection, chartRatioSection_single]
  change _ = twistingSectionsEquiv R ι ((1 : ℕ) : ℤ) i le_rfl
    ((twistingSheaf R ι ((1 : ℕ) : ℤ)).val.map (homOfLE le_top).op
      (homogeneousSection R ι 1 (coordinatePower R ι 1 (e.symm j))))
  rw [homogeneousSection_local, homogeneousChartSection,
    homogeneousChartFraction_coordinatePower_one]

/-! ### Transition units -/

variable {R} in
theorem overlapLeft_toRingHom (i l : ι) :
    (overlapLeft R i l : coordinateRing R ι i →+* coordinateOverlapRing R ι i l) =
      coordinateLeftToOverlap R ι i l :=
  rfl

variable {R} in
theorem overlapRight_toRingHom (i l : ι) :
    (overlapRight R i l : coordinateRing R ι l →+* coordinateOverlapRing R ι i l) =
      coordinateRightToOverlap R ι i l :=
  rfl

/-- The unit relating the chart points of `D₊(Xᵢ)` and `D₊(Xₗ)` on their overlap
(`ofChartSection_overlap`) is the transition unit `Xᵢ / Xₗ` of the twisting sheaves. -/
theorem overlapRight_ratio_eq_coordinateTransitionUnit (i l : ι) :
    overlapRight R i l (coordinateRatio R ι l i) = (coordinateTransitionUnit R ι i l : _) := by
  apply HomogeneousLocalization.val_injective
  rw [val_overlapRight_ratio]
  simp [coordinateTransitionUnit, coordinateOverlapRatio, Away.val_mk, pow_two]

/-- **The transition maps match.** On `D₊(Xᵢ Xₗ)`, the chart section at `l` is the chart section
at `i` multiplied by the transition unit `Xᵢ / Xₗ` of the twisting sheaves. -/
theorem overlapRight_chartRatioSection (i l : ι) (v : Fin m → R) :
    coordinateRightToOverlap R ι i l (chartRatioSection R e l v 0) =
      (coordinateTransitionUnit R ι i l : coordinateOverlapRing R ι i l) *
        coordinateLeftToOverlap R ι i l (chartRatioSection R e i v 0) := by
  rw [← overlapLeft_toRingHom, ← overlapRight_toRingHom,
    ← overlapRight_ratio_eq_coordinateTransitionUnit]
  simp only [RingHom.coe_coe, chartRatioSection_apply, map_sum, map_mul, AlgHom.commutes,
    Finset.mul_sum, overlapRight_ratio R i l (e.symm _)]
  exact Finset.sum_congr rfl fun j _ ↦ mul_left_comm _ _ _

end AlgebraicGeometry.ProjectiveSpace
