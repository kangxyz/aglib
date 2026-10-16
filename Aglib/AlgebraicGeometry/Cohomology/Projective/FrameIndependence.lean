/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.LocalCoefficients
public import Aglib.AlgebraicGeometry.ProjectiveSpace.HomogeneousSections

/-!+# Independence of the coordinate frame in the Laurent section model

The original homogeneous polynomial fractions identify the standard coordinate transition
units with their actual Laurent monomials. Consequently the homogeneous Laurent polynomial
attached to a twist section does not depend on the chosen coordinate frame.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite MvPolynomial
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- A coordinate-product open lies in every coordinate chart occurring in that product. -/
theorem coordinateProductOpen_le_chart (s : Finset ι) (i : ι) (hi : i ∈ s) :
    Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s) ≤
      coordinateOpen R ι i := by
  rw [basicOpen_coordinateProduct]
  exact iInf_le_of_le i (iInf_le_of_le hi le_rfl)

/-- The original homogeneous localization map from one coordinate chart to a finite
coordinate intersection. -/
def coordinateChartToProduct (s : Finset ι) (i : ι) (hi : i ∈ s) :
    coordinateRing R ι i →+*
      HomogeneousLocalization.Away (homogeneousSubmodule ι R) (coordinateProduct R ι s) := by
  classical
  exact HomogeneousLocalization.awayMap (homogeneousSubmodule ι R)
    (isHomogeneous_coordinateProduct R ι (s.erase i))
    (Finset.mul_prod_erase s (fun j => (X j : MvPolynomial ι R)) hi).symm

/-- Restricting an actual homogeneous polynomial chart section uses the original chart
localization map. -/
theorem homogeneousChartSection_restrict_product (s : Finset ι) (i : ι) (hi : i ∈ s)
    (n : ℕ) (p : homogeneousSubmodule ι R n) :
    sectionRestrict (ProjectiveSpace R ι) (coordinateProductOpen_le_chart R ι s i hi)
        (homogeneousChartSection R ι n p i) =
      Proj.awayToSection (homogeneousSubmodule ι R) (coordinateProduct R ι s)
        (coordinateChartToProduct R ι s i hi (homogeneousChartFraction R ι n p i)) := by
  classical
  exact (ConcreteCategory.congr_hom
    (Proj.awayMap_awayToSection (homogeneousSubmodule ι R)
      (isHomogeneous_coordinateProduct R ι (s.erase i))
      (Finset.mul_prod_erase s (fun j => (X j : MvPolynomial ι R)) hi).symm)
    (homogeneousChartFraction R ι n p i)).symm

/-- The inverse canonical section map retains the actual restricted polynomial fraction. -/
theorem coordinateProductSectionsIso_inv_homogeneousChartSection (s : Finset ι)
    (i : ι) (hi : i ∈ s) (n : ℕ) (p : homogeneousSubmodule ι R n) :
    (coordinateProductSectionsIso R ι s ⟨i, hi⟩).inv.hom
        (sectionRestrict (ProjectiveSpace R ι) (coordinateProductOpen_le_chart R ι s i hi)
          (homogeneousChartSection R ι n p i)) =
      coordinateChartToProduct R ι s i hi (homogeneousChartFraction R ι n p i) := by
  rw [homogeneousChartSection_restrict_product]
  exact (coordinateProductSectionsIso R ι s ⟨i, hi⟩).commRingCatIsoToRingEquiv.symm_apply_apply _

/-- In the original Laurent algebra, multiplying the actual chart fraction `p / Xᵢ^n`
by the standard frame `Xᵢ^n` recovers precisely the original polynomial numerator. -/
theorem coordinateChartToProduct_fraction_mul (s : Finset ι) (i : ι) (hi : i ∈ s)
    (n : ℕ) (p : homogeneousSubmodule ι R n) :
    (homogeneousLocalizationEquivCoordinateZero R s
        (coordinateChartToProduct R ι s i hi (homogeneousChartFraction R ι n p i))).val *
        (coordinateVariableUnit R s i hi ^ n).val = toCoordinateLaurent R s p.val := by
  classical
  have hprod : toCoordinateLaurent R s (coordinateProduct R ι (s.erase i)) *
      (coordinateVariableUnit R s i hi).val = (coordinateProductUnit R s).val := by
    rw [← toCoordinateLaurent_X R s i hi, ← map_mul]
    exact congrArg (toCoordinateLaurent R s)
      (Finset.prod_erase_mul s (fun j => (X j : MvPolynomial ι R)) hi)
  change coordinateLocalizationEquiv R s
      (coordinateChartToProduct R ι s i hi (homogeneousChartFraction R ι n p i)).val *
      (coordinateVariableUnit R s i hi ^ n).val = _
  simp only [coordinateChartToProduct, homogeneousChartFraction,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk]
  dsimp only [coordinateProduct]
  rw [coordinateLocalizationEquiv_mk, map_mul, map_pow, Units.val_pow_eq_pow_val]
  calc
    _ = toCoordinateLaurent R s p.val *
        ((toCoordinateLaurent R s (coordinateProduct R ι (s.erase i)) *
          (coordinateVariableUnit R s i hi).val) ^ n *
            (coordinateProductUnit R s ^ (-(n : ℤ))).val) := by
      dsimp only [coordinateProduct]
      ring
    _ = toCoordinateLaurent R s p.val := by
      rw [hprod, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
      simp

/-- The canonical inclusion of actual structure-sheaf sections into the coordinate Laurent
algebra, through their original homogeneous localization. -/
def coordinateSectionsToLaurent (s : Finset ι) (hs : s.Nonempty) :
    Γ(ProjectiveSpace R ι,
      Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s)) →+*
        coordinateLaurentAlgebra R s :=
  (coordinateLocalizationEquiv R s).toRingHom.comp
    ((algebraMap
      (HomogeneousLocalization.Away (homogeneousSubmodule ι R) (coordinateProduct R ι s))
      (Localization.Away (coordinateProduct R ι s))).comp
        (coordinateProductSectionsIso R ι s hs).inv.hom)

/-- The section-to-Laurent ring map is the underlying value of the degree-zero comparison. -/
theorem coordinateSectionsToLaurent_apply (s : Finset ι) (hs : s.Nonempty)
    (f : Γ(ProjectiveSpace R ι,
      Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s))) :
    coordinateSectionsToLaurent R ι s hs f =
      (homogeneousLocalizationEquivCoordinateZero R s
        ((coordinateProductSectionsIso R ι s hs).inv.hom f)).val := rfl

/-- The actual restricted polynomial chart section times its Laurent frame is its numerator. -/
theorem coordinateSectionsToLaurent_fraction_mul (s : Finset ι) (i : ι) (hi : i ∈ s)
    (n : ℕ) (p : homogeneousSubmodule ι R n) :
    coordinateSectionsToLaurent R ι s ⟨i, hi⟩
        (sectionRestrict (ProjectiveSpace R ι) (coordinateProductOpen_le_chart R ι s i hi)
          (homogeneousChartSection R ι n p i)) *
        (coordinateVariableUnit R s i hi ^ n).val = toCoordinateLaurent R s p.val := by
  rw [coordinateSectionsToLaurent_apply,
    coordinateProductSectionsIso_inv_homogeneousChartSection]
  exact coordinateChartToProduct_fraction_mul R ι s i hi n p

/-- The original geometric transition unit is exactly the ratio of the two native Laurent
coordinate units, on every finite coordinate intersection containing both coordinates. -/
theorem coordinateTransitionOn_laurent (s : Finset ι) (i j : ι)
    (hi : i ∈ s) (hj : j ∈ s) :
    Units.map (coordinateSectionsToLaurent R ι s ⟨i, hi⟩).toMonoidHom
        (coordinateTransitionOn R ι i j (coordinateProductOpen_le_chart R ι s i hi)
          (coordinateProductOpen_le_chart R ι s j hj)) =
      coordinateVariableUnit R s i hi * (coordinateVariableUnit R s j hj)⁻¹ := by
  let v := Units.map (coordinateSectionsToLaurent R ι s ⟨i, hi⟩).toMonoidHom
    (coordinateTransitionOn R ι i j (coordinateProductOpen_le_chart R ι s i hi)
      (coordinateProductOpen_le_chart R ι s j hj))
  have hjone : homogeneousChartSection R ι 1 (coordinatePower R ι 1 j) j = 1 := by
    simp [homogeneousChartSection]
  have ht := homogeneousChartSection_transition R ι 1 (coordinatePower R ι 1 j) i j
    (coordinateProductOpen_le_chart R ι s i hi) (coordinateProductOpen_le_chart R ι s j hj)
  rw [hjone, map_one, mul_one] at ht
  have hc := coordinateSectionsToLaurent_fraction_mul R ι s i hi 1 (coordinatePower R ι 1 j)
  rw [ht] at hc
  have hu : v⁻¹ * coordinateVariableUnit R s i hi = coordinateVariableUnit R s j hj := by
    apply Units.ext
    dsimp only [v]
    rw [Units.val_mul, Units.coe_map_inv]
    change coordinateSectionsToLaurent R ι s ⟨i, hi⟩
      ((coordinateTransitionOn R ι i j (coordinateProductOpen_le_chart R ι s i hi)
        (coordinateProductOpen_le_chart R ι s j hj))⁻¹).val *
      (coordinateVariableUnit R s i hi).val = (coordinateVariableUnit R s j hj).val
    simpa only [coordinatePower, pow_one, Nat.cast_one, zpow_neg_one,
      toCoordinateLaurent_X R s j hj] using hc
  have hu' : coordinateVariableUnit R s i hi = v * coordinateVariableUnit R s j hj := by
    rw [← hu]
    simp
  change v = _
  calc
    v = (v * coordinateVariableUnit R s j hj) * (coordinateVariableUnit R s j hj)⁻¹ := by
      simp [mul_assoc]
    _ = _ := by rw [← hu']

/-- All integer powers of the actual geometric transition retain their exact Laurent
exponents. -/
theorem coordinateTransitionOn_zpow_laurent (s : Finset ι) (i j : ι)
    (hi : i ∈ s) (hj : j ∈ s) (d : ℤ) :
    coordinateSectionsToLaurent R ι s ⟨i, hi⟩
        ((coordinateTransitionOn R ι i j (coordinateProductOpen_le_chart R ι s i hi)
          (coordinateProductOpen_le_chart R ι s j hj) ^ d).val) =
      coordinateVariableMonomial R s i hi d * coordinateVariableMonomial R s j hj (-d) := by
  change (Units.map (coordinateSectionsToLaurent R ι s ⟨i, hi⟩).toMonoidHom
    (coordinateTransitionOn R ι i j (coordinateProductOpen_le_chart R ι s i hi)
      (coordinateProductOpen_le_chart R ι s j hj) ^ d)).val = _
  rw [map_zpow, coordinateTransitionOn_laurent R ι s i j hi hj,
    mul_zpow, inv_zpow, ← zpow_neg,
    Units.val_mul, coordinateVariableUnit_zpow_val, coordinateVariableUnit_zpow_val]

/-- The homogeneous Laurent polynomial attached to an actual twist section is independent
of its chosen standard coordinate frame. -/
theorem twistingSectionsLaurentAddEquiv_frame (s : Finset ι) (i j : ι)
    (hi : i ∈ s) (hj : j ∈ s) (d : ℤ)
    (f : (twistingSheaf R ι d).val.obj
      (op (Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s)))) :
    twistingSectionsLaurentAddEquiv R ι s i hi d f =
      twistingSectionsLaurentAddEquiv R ι s j hj d f := by
  apply Subtype.ext
  change coordinateSectionsToLaurent R ι s ⟨i, hi⟩
      (twistingSectionsEquiv R ι d i (coordinateProductOpen_le_chart R ι s i hi) f) *
      coordinateVariableMonomial R s i hi d =
    coordinateSectionsToLaurent R ι s ⟨i, hi⟩
      (twistingSectionsEquiv R ι d j (coordinateProductOpen_le_chart R ι s j hj) f) *
      coordinateVariableMonomial R s j hj d
  rw [twistingSectionsEquiv_transition R ι d i j
    (coordinateProductOpen_le_chart R ι s i hi) (coordinateProductOpen_le_chart R ι s j hj),
    map_mul, coordinateTransitionOn_zpow_laurent R ι s i j hi hj, neg_neg]
  calc
    _ = coordinateSectionsToLaurent R ι s ⟨i, hi⟩
        (twistingSectionsEquiv R ι d j (coordinateProductOpen_le_chart R ι s j hj) f) *
        coordinateVariableMonomial R s j hj d *
          (coordinateVariableMonomial R s i hi (-d) *
            coordinateVariableMonomial R s i hi d) := by ring
    _ = _ := by rw [coordinateVariableMonomial_mul, neg_add_cancel,
      coordinateVariableMonomial_zero, mul_one]

/-- Arbitrary choices of coordinate frames give the same actual Laurent restriction map. -/
theorem twistingSectionsLaurentAddEquiv_restrict {s t : Finset ι} (h : s ⊆ t)
    (i j : ι) (hi : i ∈ s) (hj : j ∈ t) (d : ℤ)
    (f : (twistingSheaf R ι d).val.obj
      (op (Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s)))) :
    twistingSectionsLaurentAddEquiv R ι t j hj d
        ((twistingSheaf R ι d).val.map (homOfLE (coordinateProductOpen_le R ι h)).op f) =
      coordinateLaurentDegreeMap R h d (twistingSectionsLaurentAddEquiv R ι s i hi d f) :=
  (twistingSectionsLaurentAddEquiv_frame R ι t j i hj (h hi) d _).trans
    (twistingSectionsLaurentAddEquiv_restrict_same_frame R ι h i hi d f)

/-- The structural-ring linear section model retains every actual restriction map,
independently of the source and target coordinate frames. -/
theorem twistingSectionsLaurentLinearEquiv_restrict {s t : Finset ι} (h : s ⊆ t)
    (i j : ι) (hi : i ∈ s) (hj : j ∈ t) (d : ℤ)
    (f : (moduleSectionsPresheaf (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (twistingSheaf R ι d)).obj
        (op (Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s)))) :
    twistingSectionsLaurentLinearEquiv R ι t j hj d
        ((moduleSectionsPresheaf (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
          (twistingSheaf R ι d)).map (homOfLE (coordinateProductOpen_le R ι h)).op f) =
      coordinateLaurentDegreeMap R h d (twistingSectionsLaurentLinearEquiv R ι s i hi d f) :=
  twistingSectionsLaurentAddEquiv_restrict R ι h i j hi hj d f

/-- The Laurent polynomial attached to the restriction of an actual homogeneous global
section is the original polynomial, with its original coefficients. -/
theorem twistingSectionsLaurentAddEquiv_homogeneousSection (s : Finset ι) (i : ι)
    (hi : i ∈ s) (n : ℕ) (p : homogeneousSubmodule ι R n) :
    (twistingSectionsLaurentAddEquiv R ι s i hi (n : ℤ)
      ((twistingSheaf R ι (n : ℤ)).val.map (homOfLE le_top).op
        (homogeneousSection R ι n p))).val = toCoordinateLaurent R s p.val := by
  let hsi := coordinateProductOpen_le_chart R ι s i hi
  have hl := ((coordinateUnitCocycle R ι).zpow (-(n : ℤ))).localSectionsEquiv_restrict i
    hsi le_rfl ((twistingSheaf R ι (n : ℤ)).val.map (homOfLE le_top).op
      (homogeneousSection R ι n p))
  change twistingSectionsEquiv R ι (n : ℤ) i hsi
      ((twistingSheaf R ι (n : ℤ)).val.map (homOfLE hsi).op
        ((twistingSheaf R ι (n : ℤ)).val.map (homOfLE le_top).op
          (homogeneousSection R ι n p))) =
    sectionRestrict (ProjectiveSpace R ι) hsi
      (twistingSectionsEquiv R ι (n : ℤ) i le_rfl
        ((twistingSheaf R ι (n : ℤ)).val.map (homOfLE le_top).op
          (homogeneousSection R ι n p))) at hl
  rw [homogeneousSection_local, ← PresheafOfModules.map_comp_apply] at hl
  change twistingSectionsEquiv R ι (n : ℤ) i hsi
      ((twistingSheaf R ι (n : ℤ)).val.map (homOfLE le_top).op
        (homogeneousSection R ι n p)) =
    sectionRestrict (ProjectiveSpace R ι) hsi (homogeneousChartSection R ι n p i) at hl
  change coordinateSectionsToLaurent R ι s ⟨i, hi⟩
      (twistingSectionsEquiv R ι (n : ℤ) i hsi
        ((twistingSheaf R ι (n : ℤ)).val.map (homOfLE le_top).op
          (homogeneousSection R ι n p))) *
      coordinateVariableMonomial R s i hi (n : ℤ) = _
  rw [hl, ← coordinateVariableUnit_zpow_val R s i hi (n : ℤ)]
  simpa only [zpow_natCast] using coordinateSectionsToLaurent_fraction_mul R ι s i hi n p

end AlgebraicGeometry.Scheme.Cohomology
