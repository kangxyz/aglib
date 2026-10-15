/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Constants
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Sections
public import Aglib.RingTheory.MvPolynomial.CoordinateGrading

/-!
# Laurent monomial coefficients of actual projective twists

On a nonempty finite coordinate intersection, sections of the actual `O(d)` are identified
with the degree-`d` part of the native coordinate Laurent algebra. The map uses the original
local frame, the canonical structure-sheaf/homogeneous-localization isomorphism, the proved
degree-zero Laurent comparison, and multiplication by the actual monomial `Xᵢ^d`.
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

/-- Actual twist sections on a coordinate intersection, expressed as homogeneous Laurent
polynomials using the displayed standard frame. -/
def twistingSectionsLaurentAddEquiv (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ) :
    (twistingSheaf R ι d).val.obj
        (op (Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s))) ≃+
      coordinateGrading R s d :=
  (twistingSectionsEquiv R ι d i (by
    rw [basicOpen_coordinateProduct]
    exact iInf_le_of_le i (iInf_le_of_le hi le_rfl))).toAddEquiv.trans
      ((coordinateProductSectionsIso R ι s ⟨i, hi⟩).commRingCatIsoToRingEquiv.symm.toAddEquiv.trans
        ((homogeneousLocalizationEquivCoordinateZero R s).toAddEquiv.trans
          (coordinateGradeShift R s i hi d).toAddEquiv))

/-- The monomial coordinates of actual twist sections on a finite coordinate intersection. -/
def twistingSectionsMonomialAddEquiv (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ) :
    (twistingSheaf R ι d).val.obj
        (op (Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s))) ≃+
      ({e : coordinateExponentMonoid s // coordinateDegree s e = d} →₀ R) :=
  (twistingSectionsLaurentAddEquiv R ι s i hi d).trans
    (coordinateGradeEquivFinsupp R s d).toAddEquiv

/-- The degree-`d` monomial coordinates retain the literal Laurent coefficients. -/
theorem twistingSectionsMonomialAddEquiv_apply (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ)
    (f : (twistingSheaf R ι d).val.obj
      (op (Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s))))
    (e : {e : coordinateExponentMonoid s // coordinateDegree s e = d}) :
    twistingSectionsMonomialAddEquiv R ι s i hi d f e =
      (twistingSectionsLaurentAddEquiv R ι s i hi d f).val.coeff e.val :=
  coordinateGradeEquivFinsupp_apply R s d _ e

/-- Enlarging the finite coordinate set gives the original inclusion of intersection opens. -/
theorem coordinateProductOpen_le {s t : Finset ι} (h : s ⊆ t) :
    Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι t) ≤
      Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s) :=
  Proj.basicOpen_mono (homogeneousSubmodule ι R) _ _
    (Finset.prod_dvd_prod_of_subset s t (fun i => (X i : MvPolynomial ι R)) h)

/-- The canonical section isomorphisms retain the actual homogeneous-localization restriction. -/
theorem coordinateProductSectionsIso_inv_restrict {s t : Finset ι} (h : s ⊆ t)
    (hs : s.Nonempty) (ht : t.Nonempty)
    (f : Γ(ProjectiveSpace R ι,
      Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s))) :
    (coordinateProductSectionsIso R ι t ht).inv.hom
        (sectionRestrict (ProjectiveSpace R ι) (coordinateProductOpen_le R ι h) f) =
      coordinateHomogeneousRestriction R h ((coordinateProductSectionsIso R ι s hs).inv.hom f) := by
  classical
  let a := coordinateProductSectionsIso R ι s hs
  let b := coordinateProductSectionsIso R ι t ht
  let r := (ProjectiveSpace R ι).presheaf.map (homOfLE (coordinateProductOpen_le R ι h)).op
  have H : CommRingCat.ofHom (coordinateHomogeneousRestriction R h) ≫ b.hom = a.hom ≫ r :=
    Proj.awayMap_awayToSection (homogeneousSubmodule ι R)
      (coordinateProduct_homogeneous R (t \ s))
      ((Finset.prod_sdiff (f := fun i => (X i : MvPolynomial ι R)) h).symm.trans (mul_comm _ _))
  have Hinv : r ≫ b.inv = a.inv ≫ CommRingCat.ofHom (coordinateHomogeneousRestriction R h) := by
    apply (cancel_epi a.hom).mp
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← H]
    simp
  exact ConcreteCategory.congr_hom Hinv f

/-- In a common displayed coordinate frame, the actual restriction of twist sections becomes
the original degree-preserving Laurent coefficient inclusion. -/
theorem twistingSectionsLaurentAddEquiv_restrict_same_frame {s t : Finset ι} (h : s ⊆ t)
    (i : ι) (hi : i ∈ s) (d : ℤ)
    (f : (twistingSheaf R ι d).val.obj
      (op (Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s)))) :
    twistingSectionsLaurentAddEquiv R ι t i (h hi) d
        ((twistingSheaf R ι d).val.map (homOfLE (coordinateProductOpen_le R ι h)).op f) =
      coordinateLaurentDegreeMap R h d (twistingSectionsLaurentAddEquiv R ι s i hi d f) := by
  let hsi : Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s) ≤
      coordinateOpen R ι i := by
    rw [basicOpen_coordinateProduct]
    exact iInf_le_of_le i (iInf_le_of_le hi le_rfl)
  let hti : Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι t) ≤
      coordinateOpen R ι i := (coordinateProductOpen_le R ι h).trans hsi
  have htriv : twistingSectionsEquiv R ι d i hti
        ((twistingSheaf R ι d).val.map (homOfLE (coordinateProductOpen_le R ι h)).op f) =
      sectionRestrict (ProjectiveSpace R ι) (coordinateProductOpen_le R ι h)
        (twistingSectionsEquiv R ι d i hsi f) :=
    ((coordinateUnitCocycle R ι).zpow (-d)).localSectionsEquiv_restrict i
      (coordinateProductOpen_le R ι h) hsi f
  change coordinateGradeShift R t i (h hi) d
      (homogeneousLocalizationEquivCoordinateZero R t
        ((coordinateProductSectionsIso R ι t ⟨i, h hi⟩).inv.hom
          (twistingSectionsEquiv R ι d i hti
            ((twistingSheaf R ι d).val.map
              (homOfLE (coordinateProductOpen_le R ι h)).op f)))) =
    coordinateLaurentDegreeMap R h d
      (coordinateGradeShift R s i hi d
        (homogeneousLocalizationEquivCoordinateZero R s
          ((coordinateProductSectionsIso R ι s ⟨i, hi⟩).inv.hom
            (twistingSectionsEquiv R ι d i hsi f))))
  rw [htriv, coordinateProductSectionsIso_inv_restrict,
    homogeneousLocalizationEquivCoordinateZero_restrict]
  exact (coordinateLaurentDegreeMap_gradeShift R h i hi d _).symm

/-- Under the canonical section isomorphism, a restricted structural constant is the
original homogeneous constant fraction. -/
theorem coordinateProductSectionsIso_inv_constant (s : Finset ι) (hs : s.Nonempty) (r : R) :
    (coordinateProductSectionsIso R ι s hs).inv.hom
        (sectionRestrict (ProjectiveSpace R ι) (show
          Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s) ≤ ⊤ from le_top)
          (((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) r)) =
      HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule ι R)
        (Submonoid.powers (coordinateProduct R ι s)) (toHomogeneousSubmoduleZero R ι r) := by
  rw [constant_restriction R ι (coordinateProduct R ι s)
    (isHomogeneous_coordinateProduct R ι s) (Finset.card_pos.mpr hs)]
  exact (coordinateProductSectionsIso R ι s hs).commRingCatIsoToRingEquiv.symm_apply_apply _

/-- The Laurent comparison preserves the actual action of structural constants. -/
theorem twistingSectionsLaurentAddEquiv_smul (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ)
    (r : R) (f : (twistingSheaf R ι d).val.obj
      (op (Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s)))) :
    twistingSectionsLaurentAddEquiv R ι s i hi d
        (sectionRestrict (ProjectiveSpace R ι) (show
          Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s) ≤ ⊤ from le_top)
          (((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) r) • f) =
      r • twistingSectionsLaurentAddEquiv R ι s i hi d f := by
  let hsi : Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s) ≤
      coordinateOpen R ι i := by
    rw [basicOpen_coordinateProduct]
    exact iInf_le_of_le i (iInf_le_of_le hi le_rfl)
  change coordinateGradeShift R s i hi d
      (homogeneousLocalizationEquivCoordinateZero R s
        ((coordinateProductSectionsIso R ι s ⟨i, hi⟩).inv.hom
          (twistingSectionsEquiv R ι d i hsi (_ • f)))) =
    r • coordinateGradeShift R s i hi d
      (homogeneousLocalizationEquivCoordinateZero R s
        ((coordinateProductSectionsIso R ι s ⟨i, hi⟩).inv.hom
          (twistingSectionsEquiv R ι d i hsi f)))
  rw [map_smul]
  change coordinateGradeShift R s i hi d
      (homogeneousLocalizationEquivCoordinateZero R s
        ((coordinateProductSectionsIso R ι s ⟨i, hi⟩).inv.hom
          (_ * twistingSectionsEquiv R ι d i hsi f))) = _
  rw [map_mul, map_mul, coordinateProductSectionsIso_inv_constant]
  have hc : homogeneousLocalizationEquivCoordinateZero R s
      (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule ι R)
        (Submonoid.powers (coordinateProduct R ι s)) (toHomogeneousSubmoduleZero R ι r)) =
      algebraMap R (coordinateGrading R s 0) r :=
    homogeneousLocalizationEquivCoordinateZero_fromZero R s r
  rw [hc, ← Algebra.smul_def, map_smul]

/-- Sections on a coordinate intersection identify with the homogeneous Laurent module,
linearly for the original projective structural morphism to `Spec R`. -/
def twistingSectionsLaurentLinearEquiv (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ) :
    (moduleSectionsPresheaf (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (twistingSheaf R ι d)).obj
        (op (Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s))) ≃ₗ[R]
      coordinateGrading R s d where
  __ := twistingSectionsLaurentAddEquiv R ι s i hi d
  map_smul' r f := twistingSectionsLaurentAddEquiv_smul R ι s i hi d r f

/-- The actual structural module sections have their native finite-support monomial
coordinates, with no change to either the section map or the coefficient scalars. -/
def twistingSectionsMonomialLinearEquiv (s : Finset ι) (i : ι) (hi : i ∈ s) (d : ℤ) :
    (moduleSectionsPresheaf (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (twistingSheaf R ι d)).obj
        (op (Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s))) ≃ₗ[R]
      ({e : coordinateExponentMonoid s // coordinateDegree s e = d} →₀ R) :=
  (twistingSectionsLaurentLinearEquiv R ι s i hi d).trans (coordinateGradeEquivFinsupp R s d)

end AlgebraicGeometry.Scheme.Cohomology
