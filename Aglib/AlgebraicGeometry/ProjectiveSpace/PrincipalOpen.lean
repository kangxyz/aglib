/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.HomogeneousSections

/-!
# Coordinate intersections as actual principal opens

The original ratio `Xⱼ / Xᵢ` is a structure-sheaf function on the `i` chart. Its actual
nonvanishing open is precisely the intersection with the `j` chart. These exact function and
open identifications allow native affine section localization to clear denominators on the
standard projective cover.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The native projective chart map takes another coordinate open to the principal open
of the original coordinate ratio. -/
theorem coordinateChart_preimage_coordinateOpen (i j : ι) :
    Proj.awayι (homogeneousSubmodule ι R) (X i) (isHomogeneous_X R i) (by decide) ⁻¹ᵁ
        coordinateOpen R ι j =
      PrimeSpectrum.basicOpen (coordinateRatio R ι i j) := by
  simpa only [coordinateOpen, coordinateRatio, HomogeneousLocalization.Away.isLocalizationElem,
    pow_one] using Proj.awayι_preimage_basicOpen (𝒜 := homogeneousSubmodule ι R)
      (isHomogeneous_X R i) (by decide) (isHomogeneous_X R j) (by decide)

/-- The actual structure-sheaf function `Xⱼ / Xᵢ` on the original coordinate chart. -/
def coordinateRatioSection (i j : ι) : Γ(ProjectiveSpace R ι, coordinateOpen R ι i) :=
  Proj.awayToSection (homogeneousSubmodule ι R) (X i) (coordinateRatio R ι i j)

@[simp]
theorem coordinateRatioSection_self (i : ι) : coordinateRatioSection R ι i i = 1 := by
  simp only [coordinateRatioSection, coordinateRatio_self, map_one]

/-- The ratio function is the original local coefficient of the global coordinate section. -/
theorem coordinateRatioSection_eq_homogeneousChartSection (i j : ι) :
    coordinateRatioSection R ι i j =
      homogeneousChartSection R ι 1 (coordinatePower R ι 1 j) i := by
  change Proj.awayToSection (homogeneousSubmodule ι R) (X i) (coordinateRatio R ι i j) =
    Proj.awayToSection (homogeneousSubmodule ι R) (X i)
      (homogeneousChartFraction R ι 1 (coordinatePower R ι 1 j) i)
  congr 1
  apply HomogeneousLocalization.val_injective
  simp [coordinateRatio, homogeneousChartFraction, coordinatePower]

/-- The actual nonvanishing locus of `Xⱼ / Xᵢ` is exactly the original two-chart intersection. -/
theorem basicOpen_coordinateRatioSection (i j : ι) :
    (ProjectiveSpace R ι).basicOpen (coordinateRatioSection R ι i j) =
      coordinateOpen R ι i ⊓ coordinateOpen R ι j := by
  let U := coordinateOpen R ι i
  let e := Proj.basicOpenIsoSpec (homogeneousSubmodule ι R) (X i)
    (isHomogeneous_X R i) (by decide)
  have he : e.hom ≫
      Proj.awayι (homogeneousSubmodule ι R) (X i) (isHomogeneous_X R i) (by decide) = U.ι := by
    change e.hom ≫ (e.inv ≫ U.ι) = U.ι
    simp
  have hpre : e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (coordinateRatio R ι i j) =
      U.ι ⁻¹ᵁ coordinateOpen R ι j := by
    rw [← coordinateChart_preimage_coordinateOpen R ι i j, ← Scheme.Hom.comp_preimage, he]
  have hsection : e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (coordinateRatio R ι i j) =
      U.ι ⁻¹ᵁ (ProjectiveSpace R ι).basicOpen (coordinateRatioSection R ι i j) := by
    change (U.toSpecΓ ≫ Spec.map (Proj.awayToSection (homogeneousSubmodule ι R) (X i))) ⁻¹ᵁ
      PrimeSpectrum.basicOpen (coordinateRatio R ι i j) = _
    rw [Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen,
      Scheme.Opens.toSpecΓ_preimage_basicOpen]
    rfl
  have h := congrArg (fun W => U.ι ''ᵁ W) (hsection.symm.trans hpre)
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι] at h
  rw [inf_eq_right.mpr ((ProjectiveSpace R ι).basicOpen_le (coordinateRatioSection R ι i j))] at h
  exact h

end AlgebraicGeometry.ProjectiveSpace
