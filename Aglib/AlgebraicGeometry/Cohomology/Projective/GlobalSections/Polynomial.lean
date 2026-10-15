/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.GlobalSections.Homogeneous
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.NonnegativeZero
public import Aglib.RingTheory.MvPolynomial.CoordinatePieces
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Hom.Linear

/-!
# Original homogeneous polynomials, global sections and twist morphisms

The native nonnegative H0 weight calculation and original section augmentation identify
actual global sections of `O(m)` with the original homogeneous polynomial module.
The inverse map is exactly the previously constructed homogeneous section. Composing
with the original linear twist Hom comparison gives original polynomial multiplication
as a linear equivalence onto all twist morphisms of nonnegative degree difference.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MvPolynomial Opposite
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u) [Fintype ι]

/-- Actual global sections of a nonnegative twist are the original homogeneous polynomials,
with the original structural-ring action and polynomial coefficient maps. -/
def twistingGlobalSectionsPolynomialLinearEquiv (j : ι) (m : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := Module.compHom Γ(twistingSheaf R ι (m : ℤ), ⊤) α
    Γ(twistingSheaf R ι (m : ℤ), ⊤) ≃ₗ[R] homogeneousSubmodule ι R m := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := Module.compHom Γ(twistingSheaf R ι (m : ℤ), ⊤) α
  exact (twistingGlobalSectionsLaurentZeroLinearEquiv R ι (m : ℤ)).trans
    ((coordinateLaurentTupleNonnegativeZeroWeightsEquiv R j m).trans
      (homogeneousPieceEquivFinsupp R m).symm)

/-- The section comparison recovers exactly the original polynomial from its original
homogeneous global section, coefficient by coefficient. -/
theorem twistingGlobalSectionsPolynomialLinearEquiv_homogeneousSection (j : ι) (m : ℕ)
    (p : homogeneousSubmodule ι R m) :
    twistingGlobalSectionsPolynomialLinearEquiv R ι j m (homogeneousSection R ι m p) = p := by
  apply (homogeneousPieceEquivFinsupp R m).injective
  change homogeneousPieceEquivFinsupp R m
    ((homogeneousPieceEquivFinsupp R m).symm
      (coordinateLaurentTupleNonnegativeZeroWeightsEquiv R j m
        (twistingGlobalSectionsLaurentZeroLinearEquiv R ι (m : ℤ)
          (homogeneousSection R ι m p)))) = homogeneousPieceEquivFinsupp R m p
  rw [LinearEquiv.apply_symm_apply]
  ext a
  obtain ⟨w, rfl⟩ := (coordinatePolynomialEmptyWeightEquiv (ι := ι) m).surjective a
  rw [coordinateLaurentTupleNonnegativeZeroWeightsEquiv_homologyZeroι,
    twistingGlobalSectionsLaurentZeroLinearEquiv_homogeneousSection,
    coordinatePolynomialEmptyWeightEquiv_exponent, toCoordinateLaurent_coeff,
    homogeneousPieceEquivFinsupp_apply]

/-- Original homogeneous polynomials give all actual global sections of a nonnegative twist. -/
def homogeneousSectionLinearEquiv (j : ι) (m : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := Module.compHom Γ(twistingSheaf R ι (m : ℤ), ⊤) α
    homogeneousSubmodule ι R m ≃ₗ[R] Γ(twistingSheaf R ι (m : ℤ), ⊤) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := Module.compHom Γ(twistingSheaf R ι (m : ℤ), ⊤) α
  exact (twistingGlobalSectionsPolynomialLinearEquiv R ι j m).symm

/-- The polynomial-to-section equivalence is exactly the existing original section map. -/
theorem homogeneousSectionLinearEquiv_apply (j : ι) (m : ℕ) (p : homogeneousSubmodule ι R m) :
    homogeneousSectionLinearEquiv R ι j m p = homogeneousSection R ι m p := by
  apply (twistingGlobalSectionsPolynomialLinearEquiv R ι j m).injective
  exact ((twistingGlobalSectionsPolynomialLinearEquiv R ι j m).apply_symm_apply p).trans
    (twistingGlobalSectionsPolynomialLinearEquiv_homogeneousSection R ι j m p).symm

/-- The original actual H0 of a nonnegative twist is its homogeneous polynomial module. -/
def twistingH0PolynomialLinearEquiv (j : ι) (m : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι (m : ℤ)) 0
    Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) (twistingSheaf R ι (m : ℤ))) 0 ≃ₗ[R]
      homogeneousSubmodule ι R m := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := Module.compHom Γ(twistingSheaf R ι (m : ℤ), ⊤) α
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι (m : ℤ)) 0
  exact (moduleH0EquivOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι (m : ℤ))).trans
    (twistingGlobalSectionsPolynomialLinearEquiv R ι j m)

/-- Every original twist morphism of nonnegative degree difference is multiplication by a
unique original homogeneous polynomial, with the native structural linear category action. -/
def polynomialMultiplicationLinearEquiv (j : ι) (m : ℕ) (b : ℤ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    homogeneousSubmodule ι R m ≃ₗ[R]
      (twistingSheaf R ι b ⟶ twistingSheaf R ι ((m : ℤ) + b)) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  letI := Module.compHom Γ(twistingSheaf R ι (m : ℤ), ⊤) α
  exact (homogeneousSectionLinearEquiv R ι j m).trans
    (twistingGlobalSectionsHomLinearEquivOfHom R ι α (m : ℤ) b)

/-- The polynomial Hom equivalence retains the original actual multiplication morphism. -/
theorem polynomialMultiplicationLinearEquiv_apply (j : ι) (m : ℕ) (b : ℤ)
    (p : homogeneousSubmodule ι R m) :
    polynomialMultiplicationLinearEquiv R ι j m b p = polynomialMultiplication R ι m p b := by
  change twistingMultiplyGlobal R ι (m : ℤ) b (homogeneousSectionLinearEquiv R ι j m p) = _
  rw [homogeneousSectionLinearEquiv_apply]
  rfl

end AlgebraicGeometry.Scheme.Cohomology
