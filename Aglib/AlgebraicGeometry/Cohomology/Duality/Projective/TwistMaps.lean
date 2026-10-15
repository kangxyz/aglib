/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.GlobalSections.Polynomial
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Naturality.Degrees

/-!
# Original polynomial maps into the residue twist

A homogeneous polynomial of degree `m` multiplies `O(-m-card ι)` into the residue twist
`O(-card ι)`, with only the native equality map on the target degree. The same original
coefficient map has the literal product formula on the sole Laurent tuple complex, and
its homology map is precisely its original actual-cohomology map.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory HomologicalComplex MvPolynomial
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u) [Fintype ι]

/-- Original polynomial multiplication into the residue twist, with the canonical equality
map on its target degree. -/
def residuePolynomialMultiplication (m : ℕ) (p : homogeneousSubmodule ι R m) :
    twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ)) ⟶
      twistingSheaf R ι (-(Fintype.card ι : ℤ)) :=
  polynomialMultiplication R ι m p (-(m : ℤ) - (Fintype.card ι : ℤ)) ≫
    eqToHom (congrArg (twistingSheaf R ι)
      (show (m : ℤ) + (-(m : ℤ) - (Fintype.card ι : ℤ)) = -(Fintype.card ι : ℤ) by omega))

/-- All actual maps from the displayed negative twist into the residue twist are original
homogeneous polynomial multiplication maps, with the native structural linear action. -/
def residuePolynomialMultiplicationLinearEquiv (j : ι) (m : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    homogeneousSubmodule ι R m ≃ₗ[R]
      (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ)) ⟶
        twistingSheaf R ι (-(Fintype.card ι : ℤ))) := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  exact (polynomialMultiplicationLinearEquiv R ι j m
    (-(m : ℤ) - (Fintype.card ι : ℤ))).trans
      (CategoryTheory.Linear.homCongr R (Iso.refl _)
        (eqToIso (congrArg (twistingSheaf R ι)
          (show (m : ℤ) + (-(m : ℤ) - (Fintype.card ι : ℤ)) =
            -(Fintype.card ι : ℤ) by omega))))

/-- The residue-target Hom equivalence retains exactly the original polynomial map. -/
theorem residuePolynomialMultiplicationLinearEquiv_apply (j : ι) (m : ℕ)
    (p : homogeneousSubmodule ι R m) :
    residuePolynomialMultiplicationLinearEquiv R ι j m p =
      residuePolynomialMultiplication R ι m p := by
  change (𝟙 (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ))) ≫
    polynomialMultiplicationLinearEquiv R ι j m
      (-(m : ℤ) - (Fintype.card ι : ℤ)) p) ≫
      eqToHom (congrArg (twistingSheaf R ι)
        (show (m : ℤ) + (-(m : ℤ) - (Fintype.card ι : ℤ)) =
          -(Fintype.card ι : ℤ) by omega)) = _
  rw [Category.id_comp, polynomialMultiplicationLinearEquiv_apply]
  rfl

/-- The original Laurent polynomial chain map with its canonical residue-degree equality map. -/
def residueLaurentPolynomialMap (m : ℕ) (p : homogeneousSubmodule ι R m) :
    coordinateLaurentTupleComplex (ι := ι) R (-(m : ℤ) - (Fintype.card ι : ℤ)) ⟶
      coordinateLaurentTupleComplex (ι := ι) R (-(Fintype.card ι : ℤ)) :=
  twistingLaurentPolynomialMap R ι m p (-(m : ℤ) - (Fintype.card ι : ℤ)) ≫
    eqToHom (congrArg (coordinateLaurentTupleComplex (ι := ι) R)
      (show (m : ℤ) + (-(m : ℤ) - (Fintype.card ι : ℤ)) = -(Fintype.card ι : ℤ) by omega))

/-- Target-degree normalization leaves the literal original Laurent product unchanged. -/
theorem residueLaurentPolynomialMap_apply (m : ℕ) (p : homogeneousSubmodule ι R m)
    (q : ℕ) (x : coordinateLaurentTupleCochains (ι := ι) R
      (-(m : ℤ) - (Fintype.card ι : ℤ)) q) (a : Fin (q + 1) → ι) :
    ((residueLaurentPolynomialMap R ι m p).f q x a).val =
      toCoordinateLaurent R (coordinateTupleSet a) p.val * (x a).val := by
  have htransport (c d : ℤ) (h : c = d) (z : coordinateLaurentTupleCochains (ι := ι) R c q) :
      ((eqToHom (congrArg (coordinateLaurentTupleComplex (ι := ι) R) h)).f q z a).val =
        (z a).val := by
    subst d
    rfl
  change ((eqToHom (congrArg (coordinateLaurentTupleComplex (ι := ι) R)
    (show (m : ℤ) + (-(m : ℤ) - (Fintype.card ι : ℤ)) = -(Fintype.card ι : ℤ) by omega))).f q
      ((twistingLaurentPolynomialMap R ι m p (-(m : ℤ) - (Fintype.card ι : ℤ))).f q x) a).val = _
  have hdeg : (m : ℤ) + (-(m : ℤ) - (Fintype.card ι : ℤ)) =
      -(Fintype.card ι : ℤ) := by omega
  rw [htransport _ _ hdeg]
  exact twistingLaurentPolynomialMap_apply R ι m p (-(m : ℤ) - (Fintype.card ι : ℤ)) q x a

/-- The normalized original Laurent map induces precisely the original actual coefficient
cohomology map of polynomial multiplication into the residue twist, in every degree. -/
theorem twistingLaurentCohomologyLinearEquiv_residuePolynomial (m : ℕ)
    (p : homogeneousSubmodule ι R m) (q : ℕ)
    (x : (coordinateLaurentTupleComplex (ι := ι) R
      (-(m : ℤ) - (Fintype.card ι : ℤ))).homology q) :
    twistingLaurentCohomologyLinearEquiv R ι (-(Fintype.card ι : ℤ)) q
        (homologyMap (residueLaurentPolynomialMap R ι m p) q x) =
      Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
        (residuePolynomialMultiplication R ι m p)) q
          (twistingLaurentCohomologyLinearEquiv R ι
            (-(m : ℤ) - (Fintype.card ι : ℤ)) q x) := by
  rw [residueLaurentPolynomialMap, homologyMap_comp]
  change twistingLaurentCohomologyLinearEquiv R ι (-(Fintype.card ι : ℤ)) q
    (homologyMap (eqToHom (congrArg (coordinateLaurentTupleComplex (ι := ι) R)
      (show (m : ℤ) + (-(m : ℤ) - (Fintype.card ι : ℤ)) = -(Fintype.card ι : ℤ) by omega))) q
        (homologyMap (twistingLaurentPolynomialMap R ι m p
          (-(m : ℤ) - (Fintype.card ι : ℤ))) q x)) = _
  have hdeg : (m : ℤ) + (-(m : ℤ) - (Fintype.card ι : ℤ)) =
      -(Fintype.card ι : ℤ) := by omega
  rw [twistingLaurentCohomologyLinearEquiv_eqToHom R ι _ _ hdeg q,
    twistingLaurentCohomologyLinearEquiv_polynomial]
  rw [residuePolynomialMultiplication,
    CategoryTheory.Functor.map_comp, Sheaf.H.map_comp_apply]

end AlgebraicGeometry.Scheme.Cohomology
