/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.Multiplication
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Modules.Naturality

/-!
# The original cohomology action of projective polynomial multiplication

The all-degree projective Cech comparison is natural for actual twist coefficient morphisms.
Consequently the literal polynomial product on the Laurent tuple complex induces precisely
the original `Sheaf.H.map` of geometric polynomial multiplication, with no replacement
cohomology or unproved comparison premise.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Cech HomologicalComplex
open Opposite MvPolynomial AlgebraicGeometry.ProjectiveSpace

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- In every degree, the projective structural-ring comparison preserves each actual
morphism between the integer twists. -/
theorem twistingCechCohomologyLinearEquivAll_naturality (d e : ℤ)
    (φ : twistingSheaf R ι d ⟶ twistingSheaf R ι e) (q : ℕ)
    (x : ((cechComplexFunctor (coordinateOpen R ι)).obj
      (twistingStructuralSections R ι d)).homology q) :
    twistingCechCohomologyLinearEquivAll R ι e q
        (homologyMap (moduleCechMap (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
          (coordinateOpen R ι) φ) q x) =
      Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map φ) q
        (twistingCechCohomologyLinearEquivAll R ι d q x) := by
  let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  have haff (p : ℕ) (a : Fin (p + 1) → ι) :
      IsAffineOpen (∏ᶜ fun k => coordinateOpen R ι (a k)) := by
    change IsAffineOpen (tupleOpen (coordinateOpen R ι) p a)
    rw [coordinateTupleOpen_eq, basicOpen_coordinateProduct]
    exact isAffineOpen_coordinateIntersection R ι (coordinateTupleSet a)
      ⟨a 0, (mem_coordinateTupleSet a (a 0)).mpr ⟨0, rfl⟩⟩
  cases q with
  | zero =>
    exact moduleCechCohomologyLinearEquivZero_naturality (ProjectiveSpace R ι) α
      (coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι) φ x
  | succ q =>
    exact moduleCechCohomologyLinearEquiv_naturality (ProjectiveSpace R ι) α
      (coordinateOpen R ι) (iSup_coordinateOpen_eq_top R ι) haff
      (injectiveResolution (moduleAddSheaf (ProjectiveSpace R ι) (twistingSheaf R ι d)))
      (injectiveResolution (moduleAddSheaf (ProjectiveSpace R ι) (twistingSheaf R ι e))) φ q x

/-- The literal Laurent polynomial cochain map induces precisely the original cohomology
map of the actual geometric coefficient morphism, in every degree. -/
theorem twistingLaurentCohomologyLinearEquiv_polynomial (n : ℕ)
    (p : homogeneousSubmodule ι R n) (b : ℤ) (q : ℕ)
    (x : (coordinateLaurentTupleComplex (ι := ι) R b).homology q) :
    twistingLaurentCohomologyLinearEquiv R ι ((n : ℤ) + b) q
        (homologyMap (twistingLaurentPolynomialMap R ι n p b) q x) =
      Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
        (polynomialMultiplication R ι n p b)) q
          (twistingLaurentCohomologyLinearEquiv R ι b q x) := by
  have hw : twistingLaurentPolynomialMap R ι n p b ≫
      (twistingCechLaurentIso R ι ((n : ℤ) + b)).inv =
    (twistingCechLaurentIso R ι b).inv ≫ twistingCechPolynomialMap R ι n p b := by
    simp only [twistingLaurentPolynomialMap, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h := congrArg (fun f => homologyMap f q) hw
  simp only [homologyMap_comp] at h
  have hx := ConcreteCategory.congr_hom h x
  change homologyMap (twistingCechLaurentIso R ι ((n : ℤ) + b)).inv q
      (homologyMap (twistingLaurentPolynomialMap R ι n p b) q x) =
    homologyMap (twistingCechPolynomialMap R ι n p b) q
      (homologyMap (twistingCechLaurentIso R ι b).inv q x) at hx
  change twistingCechCohomologyLinearEquivAll R ι ((n : ℤ) + b) q
      (homologyMap (twistingCechLaurentIso R ι ((n : ℤ) + b)).inv q
        (homologyMap (twistingLaurentPolynomialMap R ι n p b) q x)) =
    Sheaf.H.map ((SheafOfModules.toSheaf (ProjectiveSpace R ι).ringCatSheaf).map
      (polynomialMultiplication R ι n p b)) q
        (twistingCechCohomologyLinearEquivAll R ι b q
          (homologyMap (twistingCechLaurentIso R ι b).inv q x))
  rw [hx]
  exact twistingCechCohomologyLinearEquivAll_naturality R ι b ((n : ℤ) + b)
    (polynomialMultiplication R ι n p b) q _

end AlgebraicGeometry.Scheme.Cohomology
