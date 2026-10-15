/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting
public import Aglib.AlgebraicGeometry.ProjectiveSpace.CoordinateRing

/-!
# Homogeneous polynomials and sections of projective twists

A homogeneous degree-`n` polynomial gives the chart fraction `p / Xᵢ^n`.
These actual homogeneous-localization elements have the `O(n)` transition rule under the
canonical overlap maps. This identifies polynomial numerators with the standard local frames.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The actual localization map from the first chart ring to the two-chart overlap. -/
def coordinateLeftToOverlap (i j : ι) :
    coordinateRing R ι i →+* coordinateOverlapRing R ι i j :=
  awayMap (homogeneousSubmodule ι R) (isHomogeneous_X R j) rfl

/-- The actual localization map from the second chart ring to the two-chart overlap. -/
def coordinateRightToOverlap (i j : ι) :
    coordinateRing R ι j →+* coordinateOverlapRing R ι i j :=
  awayMap (homogeneousSubmodule ι R) (isHomogeneous_X R i) (mul_comm _ _)

/-- A homogeneous polynomial expressed in the standard frame on a coordinate chart. -/
def homogeneousChartFraction (n : ℕ) (p : homogeneousSubmodule ι R n) (i : ι) :
    coordinateRing R ι i :=
  Away.mk (homogeneousSubmodule ι R) (isHomogeneous_X R i) n p.val
    (by simpa only [smul_eq_mul, mul_one] using p.property)

/-- Multiplication by the nth power of `Xᵢ / Xⱼ` changes the homogeneous polynomial fraction
from the `i` chart frame to the `j` chart frame. -/
theorem transitionUnit_pow_mul_homogeneousChartFraction (n : ℕ)
    (p : homogeneousSubmodule ι R n) (i j : ι) :
    ((coordinateTransitionUnit R ι i j ^ n : (coordinateOverlapRing R ι i j)ˣ) :
        coordinateOverlapRing R ι i j) *
      coordinateLeftToOverlap R ι i j (homogeneousChartFraction R ι n p i) =
      coordinateRightToOverlap R ι i j (homogeneousChartFraction R ι n p j) := by
  apply HomogeneousLocalization.val_injective
  simp only [Units.val_pow_eq_pow_val, coordinateTransitionUnit, coordinateOverlapRatio,
    coordinateLeftToOverlap, coordinateRightToOverlap, homogeneousChartFraction, awayMap_mk,
    HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow, Away.val_mk]
  rw [Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_iff_eq']
  congr 1
  simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow, pow_one, mul_pow]
  ring

/-- Homogeneous polynomial fractions satisfy precisely the actual `O(n)` transition rule. -/
theorem homogeneousChartFraction_transition (n : ℕ)
    (p : homogeneousSubmodule ι R n) (i j : ι) :
    coordinateLeftToOverlap R ι i j (homogeneousChartFraction R ι n p i) =
      ((coordinateTransitionUnit R ι i j ^ (-(n : ℤ)) :
        (coordinateOverlapRing R ι i j)ˣ) : coordinateOverlapRing R ι i j) *
      coordinateRightToOverlap R ι i j (homogeneousChartFraction R ι n p j) := by
  have hu : (coordinateTransitionUnit R ι i j ^ (-(n : ℤ)) :
      (coordinateOverlapRing R ι i j)ˣ) * coordinateTransitionUnit R ι i j ^ n = 1 := by simp
  have h := congrArg (fun z : coordinateOverlapRing R ι i j =>
      (coordinateTransitionUnit R ι i j ^ (-(n : ℤ)) :
        (coordinateOverlapRing R ι i j)ˣ).val * z)
    (transitionUnit_pow_mul_homogeneousChartFraction R ι n p i j)
  simpa only [← mul_assoc, ← Units.val_mul, hu, Units.val_one, one_mul] using h

/-- The actual structure-sheaf function `p / Xᵢ^n` on the standard coordinate chart. -/
def homogeneousChartSection (n : ℕ) (p : homogeneousSubmodule ι R n) (i : ι) :
    Γ(ProjectiveSpace R ι, coordinateOpen R ι i) :=
  Proj.awayToSection (homogeneousSubmodule ι R) (X i) (homogeneousChartFraction R ι n p i)

theorem homogeneousChartSection_restrict_left (n : ℕ) (p : homogeneousSubmodule ι R n)
    (i j : ι) :
    sectionRestrict (ProjectiveSpace R ι)
        (Proj.basicOpen_mono (homogeneousSubmodule ι R) (X i) (X i * X j) ⟨X j, rfl⟩)
        (homogeneousChartSection R ι n p i) =
      Proj.awayToSection (homogeneousSubmodule ι R) (X i * X j)
        (coordinateLeftToOverlap R ι i j (homogeneousChartFraction R ι n p i)) :=
  (ConcreteCategory.congr_hom
    (Proj.awayMap_awayToSection (homogeneousSubmodule ι R) (f := X i)
      (isHomogeneous_X R j) rfl) (homogeneousChartFraction R ι n p i)).symm

theorem homogeneousChartSection_restrict_right (n : ℕ) (p : homogeneousSubmodule ι R n)
    (i j : ι) :
    sectionRestrict (ProjectiveSpace R ι)
        (Proj.basicOpen_mono (homogeneousSubmodule ι R) (X j) (X i * X j)
          ⟨X i, mul_comm _ _⟩) (homogeneousChartSection R ι n p j) =
      Proj.awayToSection (homogeneousSubmodule ι R) (X i * X j)
        (coordinateRightToOverlap R ι i j (homogeneousChartFraction R ι n p j)) :=
  (ConcreteCategory.congr_hom
    (Proj.awayMap_awayToSection (homogeneousSubmodule ι R) (f := X j)
      (isHomogeneous_X R i) (mul_comm _ _)) (homogeneousChartFraction R ι n p j)).symm

/-- The polynomial chart functions satisfy the actual twisting transition equation after
restriction to every common subopen. -/
theorem homogeneousChartSection_transition (n : ℕ) (p : homogeneousSubmodule ι R n)
    (i j : ι) {V : (ProjectiveSpace R ι).Opens}
    (hi : V ≤ coordinateOpen R ι i) (hj : V ≤ coordinateOpen R ι j) :
    sectionRestrict (ProjectiveSpace R ι) hi (homogeneousChartSection R ι n p i) =
      ((coordinateTransitionOn R ι i j hi hj ^ (-(n : ℤ)) :
        (Γ(ProjectiveSpace R ι, V))ˣ) : Γ(ProjectiveSpace R ι, V)) *
      sectionRestrict (ProjectiveSpace R ι) hj (homogeneousChartSection R ι n p j) := by
  let hV := le_basicOpen_coordinate_mul R ι i j hi hj
  let φ : coordinateOverlapRing R ι i j →+* Γ(ProjectiveSpace R ι, V) :=
    (sectionRestrict (ProjectiveSpace R ι) hV).comp
      (Proj.awayToSection (homogeneousSubmodule ι R) (X i * X j)).hom
  have hleft : φ (coordinateLeftToOverlap R ι i j (homogeneousChartFraction R ι n p i)) =
      sectionRestrict (ProjectiveSpace R ι) hi (homogeneousChartSection R ι n p i) := by
    change sectionRestrict (ProjectiveSpace R ι) hV _ = _
    rw [← homogeneousChartSection_restrict_left, sectionRestrict_comp]
    rfl
  have hright : φ (coordinateRightToOverlap R ι i j (homogeneousChartFraction R ι n p j)) =
      sectionRestrict (ProjectiveSpace R ι) hj (homogeneousChartSection R ι n p j) := by
    change sectionRestrict (ProjectiveSpace R ι) hV _ = _
    rw [← homogeneousChartSection_restrict_right, sectionRestrict_comp]
    rfl
  have hunit : φ (coordinateTransitionUnit R ι i j ^ (-(n : ℤ)) :
        (coordinateOverlapRing R ι i j)ˣ) =
      ((coordinateTransitionOn R ι i j hi hj ^ (-(n : ℤ)) :
        (Γ(ProjectiveSpace R ι, V))ˣ) : Γ(ProjectiveSpace R ι, V)) := by
    change (Units.map φ.toMonoidHom (coordinateTransitionUnit R ι i j ^ (-(n : ℤ)))).val = _
    rw [map_zpow]
    rfl
  have h := congrArg φ (homogeneousChartFraction_transition R ι n p i j)
  rwa [map_mul, hleft, hright, hunit] at h

/-- Every homogeneous degree-`n` polynomial defines a global section of the actual `O(n)`. -/
def homogeneousSection (n : ℕ) (p : homogeneousSubmodule ι R n) :
    (twistingSheaf R ι (n : ℤ)).val.obj (Opposite.op ⊤) := by
  change ((coordinateUnitCocycle R ι).zpow (-(n : ℤ))).Sections ⊤
  refine ⟨fun i => sectionRestrict (ProjectiveSpace R ι) inf_le_right
    (homogeneousChartSection R ι n p i), ?_⟩
  intro V hV i j hi hj
  simp only [sectionRestrict_comp, UnitCocycle.zpow_transitionOn,
    coordinateUnitCocycle_transitionOn]
  exact homogeneousChartSection_transition R ι n p i j hi hj

/-- The actual global polynomial section is `p / Xᵢ^n` in the specified local frame. -/
theorem homogeneousSection_local (n : ℕ) (p : homogeneousSubmodule ι R n) (i : ι) :
    twistingSectionsEquiv R ι (n : ℤ) i le_rfl
      ((twistingSheaf R ι (n : ℤ)).val.map (homOfLE le_top).op
        (homogeneousSection R ι n p)) = homogeneousChartSection R ι n p i := by
  change sectionRestrict (ProjectiveSpace R ι) (le_inf le_rfl le_rfl)
    (sectionRestrict (ProjectiveSpace R ι) (inf_le_inf le_top le_rfl)
      (sectionRestrict (ProjectiveSpace R ι) inf_le_right
        (homogeneousChartSection R ι n p i))) = _
  rw [sectionRestrict_comp, sectionRestrict_comp, sectionRestrict_refl]

/-- The nth power of a coordinate, regarded as a homogeneous polynomial of degree `n`. -/
def coordinatePower (n : ℕ) (i : ι) : homogeneousSubmodule ι R n :=
  ⟨X i ^ n, by simpa only [mem_homogeneousSubmodule, one_mul] using
    (isHomogeneous_X R i).pow n⟩

@[simp]
theorem homogeneousChartFraction_coordinatePower (n : ℕ) (i : ι) :
    homogeneousChartFraction R ι n (coordinatePower R ι n i) i = 1 := by
  apply HomogeneousLocalization.val_injective
  simp [homogeneousChartFraction, coordinatePower]

/-- The global coordinate-power section is a generator in its own standard chart. -/
theorem homogeneousSection_coordinatePower_local (n : ℕ) (i : ι) :
    twistingSectionsEquiv R ι (n : ℤ) i le_rfl
      ((twistingSheaf R ι (n : ℤ)).val.map (homOfLE le_top).op
        (homogeneousSection R ι n (coordinatePower R ι n i))) = 1 := by
  rw [homogeneousSection_local]
  simp [homogeneousChartSection]

end AlgebraicGeometry.ProjectiveSpace
