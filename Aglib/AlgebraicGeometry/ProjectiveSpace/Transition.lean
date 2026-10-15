/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Basic

/-!
# Projective coordinate transition units

On the overlap of two coordinate charts, `Xᵢ / Xⱼ` is the degree-zero fraction
`Xᵢ² / (Xᵢ Xⱼ)`. This file constructs that actual unit and proves its cocycle equation under
the canonical localization maps to triple intersections. Integer powers give the transition
units for every twist. No field, Noetherianity or finite-coordinate assumption is used.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory MvPolynomial HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The native degree-zero ring on a two-coordinate intersection. -/
abbrev coordinateOverlapRing (i j : ι) :=
  HomogeneousLocalization.Away (homogeneousSubmodule ι R) (X i * X j)

/-- The native degree-zero ring on a three-coordinate intersection. -/
abbrev coordinateTripleRing (i j k : ι) :=
  HomogeneousLocalization.Away (homogeneousSubmodule ι R) (X i * X j * X k)

/-- The homogeneous fraction `Xₖ² / (Xᵢ Xⱼ)` on a two-coordinate intersection. -/
def coordinateOverlapRatio (i j k : ι) : coordinateOverlapRing R ι i j :=
  Away.mk (homogeneousSubmodule ι R) ((isHomogeneous_X R i).mul (isHomogeneous_X R j))
    1 (X k ^ 2) (by simpa using (isHomogeneous_X R k).pow 2)

/-- The two coordinate ratios on a two-chart overlap are inverse. -/
theorem coordinateOverlapRatio_mul (i j : ι) :
    coordinateOverlapRatio R ι i j i * coordinateOverlapRatio R ι i j j = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [coordinateOverlapRatio, HomogeneousLocalization.val_mul, Away.val_mk,
    HomogeneousLocalization.val_one]
  rw [Localization.mk_mul, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simp only [one_mul]
  congr 1
  simp only [Submonoid.coe_mul]
  ring

/-- The actual unit `Xᵢ / Xⱼ` on the overlap of the `i` and `j` charts. -/
def coordinateTransitionUnit (i j : ι) : (coordinateOverlapRing R ι i j)ˣ where
  val := coordinateOverlapRatio R ι i j i
  inv := coordinateOverlapRatio R ι i j j
  val_inv := coordinateOverlapRatio_mul R ι i j
  inv_val := by rw [mul_comm, coordinateOverlapRatio_mul]

/-- Restriction from the first two charts to the triple intersection. -/
def coordinateOverlapToTriple₀₁ (i j k : ι) :
    coordinateOverlapRing R ι i j →+* coordinateTripleRing R ι i j k :=
  awayMap (homogeneousSubmodule ι R) (isHomogeneous_X R k) rfl

/-- Restriction from the last two charts to the triple intersection. -/
def coordinateOverlapToTriple₁₂ (i j k : ι) :
    coordinateOverlapRing R ι j k →+* coordinateTripleRing R ι i j k :=
  awayMap (homogeneousSubmodule ι R) (isHomogeneous_X R i) (by ring)

/-- Restriction from the first and last charts to the triple intersection. -/
def coordinateOverlapToTriple₀₂ (i j k : ι) :
    coordinateOverlapRing R ι i k →+* coordinateTripleRing R ι i j k :=
  awayMap (homogeneousSubmodule ι R) (isHomogeneous_X R j) (by ring)

/-- The actual homogeneous coordinate fractions satisfy the cocycle equation. -/
theorem coordinateOverlapRatio_cocycle (i j k : ι) :
    coordinateOverlapToTriple₀₁ R ι i j k (coordinateOverlapRatio R ι i j i) *
      coordinateOverlapToTriple₁₂ R ι i j k (coordinateOverlapRatio R ι j k j) =
        coordinateOverlapToTriple₀₂ R ι i j k (coordinateOverlapRatio R ι i k i) := by
  apply HomogeneousLocalization.val_injective
  simp only [coordinateOverlapToTriple₀₁, coordinateOverlapToTriple₁₂,
    coordinateOverlapToTriple₀₂, coordinateOverlapRatio, awayMap_mk,
    HomogeneousLocalization.val_mul, Away.val_mk]
  rw [Localization.mk_mul, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq']
  congr 1
  simp only [Submonoid.coe_mul]
  ring

/-- The coordinate transition units form a cocycle under the canonical localization maps. -/
theorem coordinateTransitionUnit_cocycle (i j k : ι) :
    Units.map (coordinateOverlapToTriple₀₁ R ι i j k).toMonoidHom
        (coordinateTransitionUnit R ι i j) *
      Units.map (coordinateOverlapToTriple₁₂ R ι i j k).toMonoidHom
        (coordinateTransitionUnit R ι j k) =
      Units.map (coordinateOverlapToTriple₀₂ R ι i j k).toMonoidHom
        (coordinateTransitionUnit R ι i k) := by
  apply Units.ext
  exact coordinateOverlapRatio_cocycle R ι i j k

/-- Every integer power of the coordinate transition cocycle again satisfies the cocycle law. -/
theorem coordinateTransitionUnit_zpow_cocycle (i j k : ι) (n : ℤ) :
    Units.map (coordinateOverlapToTriple₀₁ R ι i j k).toMonoidHom
        (coordinateTransitionUnit R ι i j ^ n) *
      Units.map (coordinateOverlapToTriple₁₂ R ι i j k).toMonoidHom
        (coordinateTransitionUnit R ι j k ^ n) =
      Units.map (coordinateOverlapToTriple₀₂ R ι i j k).toMonoidHom
        (coordinateTransitionUnit R ι i k ^ n) := by
  simp only [map_zpow, ← mul_zpow, coordinateTransitionUnit_cocycle]

/-- The coordinate transition unit as an actual structure-sheaf section on the overlap. -/
def coordinateTransitionSectionUnit (i j : ι) :
    (Γ(ProjectiveSpace R ι, Proj.basicOpen (homogeneousSubmodule ι R) (X i * X j)))ˣ :=
  Units.map (Proj.awayToSection (homogeneousSubmodule ι R) (X i * X j)).hom.toMonoidHom
    (coordinateTransitionUnit R ι i j)

/-- Actual structure-sheaf restriction from the first two charts to the triple intersection. -/
def coordinateOverlapSectionsToTriple₀₁ (i j k : ι) :
    Γ(ProjectiveSpace R ι, Proj.basicOpen (homogeneousSubmodule ι R) (X i * X j)) →+*
      Γ(ProjectiveSpace R ι, Proj.basicOpen (homogeneousSubmodule ι R) (X i * X j * X k)) :=
  ((ProjectiveSpace R ι).presheaf.map
    (homOfLE (Proj.basicOpen_mono (homogeneousSubmodule ι R) _ _ ⟨X k, rfl⟩)).op).hom

/-- Actual structure-sheaf restriction from the last two charts to the triple intersection. -/
def coordinateOverlapSectionsToTriple₁₂ (i j k : ι) :
    Γ(ProjectiveSpace R ι, Proj.basicOpen (homogeneousSubmodule ι R) (X j * X k)) →+*
      Γ(ProjectiveSpace R ι, Proj.basicOpen (homogeneousSubmodule ι R) (X i * X j * X k)) :=
  ((ProjectiveSpace R ι).presheaf.map
    (homOfLE (Proj.basicOpen_mono (homogeneousSubmodule ι R) _ _ ⟨X i, by ring⟩)).op).hom

/-- Actual structure-sheaf restriction from the first and last charts to the triple intersection. -/
def coordinateOverlapSectionsToTriple₀₂ (i j k : ι) :
    Γ(ProjectiveSpace R ι, Proj.basicOpen (homogeneousSubmodule ι R) (X i * X k)) →+*
      Γ(ProjectiveSpace R ι, Proj.basicOpen (homogeneousSubmodule ι R) (X i * X j * X k)) :=
  ((ProjectiveSpace R ι).presheaf.map
    (homOfLE (Proj.basicOpen_mono (homogeneousSubmodule ι R) _ _ ⟨X j, by ring⟩)).op).hom

private theorem coordinateOverlapSectionsToTriple₀₁_awayToSection (i j k : ι)
    (z : coordinateOverlapRing R ι i j) :
    coordinateOverlapSectionsToTriple₀₁ R ι i j k
        (Proj.awayToSection (homogeneousSubmodule ι R) (X i * X j) z) =
      Proj.awayToSection (homogeneousSubmodule ι R) (X i * X j * X k)
        (coordinateOverlapToTriple₀₁ R ι i j k z) :=
  (ConcreteCategory.congr_hom
    (Proj.awayMap_awayToSection (homogeneousSubmodule ι R) (f := X i * X j)
      (isHomogeneous_X R k) rfl) z).symm

private theorem coordinateOverlapSectionsToTriple₁₂_awayToSection (i j k : ι)
    (z : coordinateOverlapRing R ι j k) :
    coordinateOverlapSectionsToTriple₁₂ R ι i j k
        (Proj.awayToSection (homogeneousSubmodule ι R) (X j * X k) z) =
      Proj.awayToSection (homogeneousSubmodule ι R) (X i * X j * X k)
        (coordinateOverlapToTriple₁₂ R ι i j k z) :=
  (ConcreteCategory.congr_hom
    (Proj.awayMap_awayToSection (homogeneousSubmodule ι R) (f := X j * X k)
      (x := X i * X j * X k) (isHomogeneous_X R i) (by ring)) z).symm

private theorem coordinateOverlapSectionsToTriple₀₂_awayToSection (i j k : ι)
    (z : coordinateOverlapRing R ι i k) :
    coordinateOverlapSectionsToTriple₀₂ R ι i j k
        (Proj.awayToSection (homogeneousSubmodule ι R) (X i * X k) z) =
      Proj.awayToSection (homogeneousSubmodule ι R) (X i * X j * X k)
        (coordinateOverlapToTriple₀₂ R ι i j k z) :=
  (ConcreteCategory.congr_hom
    (Proj.awayMap_awayToSection (homogeneousSubmodule ι R) (f := X i * X k)
      (x := X i * X j * X k) (isHomogeneous_X R j) (by ring)) z).symm

/-- The actual structure-sheaf transition units satisfy the cocycle law with the actual
restriction maps on the triple intersection. -/
theorem coordinateTransitionSectionUnit_cocycle (i j k : ι) :
    Units.map (coordinateOverlapSectionsToTriple₀₁ R ι i j k).toMonoidHom
        (coordinateTransitionSectionUnit R ι i j) *
      Units.map (coordinateOverlapSectionsToTriple₁₂ R ι i j k).toMonoidHom
        (coordinateTransitionSectionUnit R ι j k) =
      Units.map (coordinateOverlapSectionsToTriple₀₂ R ι i j k).toMonoidHom
        (coordinateTransitionSectionUnit R ι i k) := by
  apply Units.ext
  change coordinateOverlapSectionsToTriple₀₁ R ι i j k
        (Proj.awayToSection (homogeneousSubmodule ι R) (X i * X j)
          (coordinateOverlapRatio R ι i j i)) *
      coordinateOverlapSectionsToTriple₁₂ R ι i j k
        (Proj.awayToSection (homogeneousSubmodule ι R) (X j * X k)
          (coordinateOverlapRatio R ι j k j)) =
      coordinateOverlapSectionsToTriple₀₂ R ι i j k
        (Proj.awayToSection (homogeneousSubmodule ι R) (X i * X k)
          (coordinateOverlapRatio R ι i k i))
  rw [coordinateOverlapSectionsToTriple₀₁_awayToSection,
    coordinateOverlapSectionsToTriple₁₂_awayToSection,
    coordinateOverlapSectionsToTriple₀₂_awayToSection, ← map_mul,
    coordinateOverlapRatio_cocycle]

/-- Every integer twist of the actual section-valued cocycle satisfies the cocycle law. -/
theorem coordinateTransitionSectionUnit_zpow_cocycle (i j k : ι) (n : ℤ) :
    Units.map (coordinateOverlapSectionsToTriple₀₁ R ι i j k).toMonoidHom
        (coordinateTransitionSectionUnit R ι i j ^ n) *
      Units.map (coordinateOverlapSectionsToTriple₁₂ R ι i j k).toMonoidHom
        (coordinateTransitionSectionUnit R ι j k ^ n) =
      Units.map (coordinateOverlapSectionsToTriple₀₂ R ι i j k).toMonoidHom
        (coordinateTransitionSectionUnit R ι i k ^ n) := by
  simp only [map_zpow, ← mul_zpow, coordinateTransitionSectionUnit_cocycle]

end AlgebraicGeometry.ProjectiveSpace
