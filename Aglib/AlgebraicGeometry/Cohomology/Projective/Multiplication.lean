/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.LaurentComparison
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Multiplication

/-!
# The original twist multiplication in Laurent coordinates

The actual sheaf multiplication maps become the original Laurent product under the proved
section comparison. In particular, a homogeneous polynomial coefficient morphism is literally
multiplication by its unchanged polynomial numerator on every tuple intersection.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Cech Opposite MvPolynomial
open AlgebraicGeometry.ProjectiveSpace

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Actual twist-section multiplication is the original product of Laurent polynomials. -/
theorem twistingSectionsLaurentAddEquiv_mul (s : Finset ι) (i : ι) (hi : i ∈ s)
    (a b : ℤ)
    (f : (twistingSheaf R ι a).val.obj
      (op (Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s))))
    (g : (twistingSheaf R ι b).val.obj
      (op (Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s)))) :
    (twistingSectionsLaurentAddEquiv R ι s i hi (a + b)
        (twistingSectionMul R ι a b _ f g)).val =
      (twistingSectionsLaurentAddEquiv R ι s i hi a f).val *
        (twistingSectionsLaurentAddEquiv R ι s i hi b g).val := by
  let hsi := coordinateProductOpen_le_chart R ι s i hi
  change coordinateSectionsToLaurent R ι s ⟨i, hi⟩
      (twistingSectionsEquiv R ι (a + b) i hsi (twistingSectionMul R ι a b _ f g)) *
      coordinateVariableMonomial R s i hi (a + b) =
    (coordinateSectionsToLaurent R ι s ⟨i, hi⟩ (twistingSectionsEquiv R ι a i hsi f) *
      coordinateVariableMonomial R s i hi a) *
    (coordinateSectionsToLaurent R ι s ⟨i, hi⟩ (twistingSectionsEquiv R ι b i hsi g) *
      coordinateVariableMonomial R s i hi b)
  rw [twistingSectionsEquiv_mul, map_mul, ← coordinateVariableMonomial_mul R s i hi a b]
  ring

/-- The actual polynomial coefficient morphism becomes multiplication by the original
polynomial on every finite coordinate intersection. -/
theorem polynomialMultiplication_laurent (n : ℕ) (p : homogeneousSubmodule ι R n) (b : ℤ)
    (s : Finset ι) (i : ι) (hi : i ∈ s)
    (t : (twistingSheaf R ι b).val.obj
      (op (Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s)))) :
    (twistingSectionsLaurentAddEquiv R ι s i hi ((n : ℤ) + b)
        ((polynomialMultiplication R ι n p b).val.app
          (op (Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι s))) t)).val =
      toCoordinateLaurent R s p.val * (twistingSectionsLaurentAddEquiv R ι s i hi b t).val := by
  change (twistingSectionsLaurentAddEquiv R ι s i hi ((n : ℤ) + b)
    (twistingSectionMul R ι (n : ℤ) b _
      ((twistingSheaf R ι (n : ℤ)).val.map (homOfLE le_top).op
        (homogeneousSection R ι n p)) t)).val = _
  rw [twistingSectionsLaurentAddEquiv_mul,
    twistingSectionsLaurentAddEquiv_homogeneousSection]

/-- The coefficient morphism retains literal polynomial multiplication on each original
categorical tuple intersection, including repeated coordinates. -/
theorem polynomialMultiplication_tuple (n : ℕ) (p : homogeneousSubmodule ι R n) (b : ℤ)
    (q : ℕ) (a : Fin (q + 1) → ι)
    (x : (twistingStructuralSections R ι b).obj
      (op (tupleOpen (coordinateOpen R ι) q a))) :
    (twistingTupleSectionsLinearEquiv R ι ((n : ℤ) + b) q a
        ((polynomialMultiplication R ι n p b).val.app
          (op (tupleOpen (coordinateOpen R ι) q a)) x)).val =
      toCoordinateLaurent R (coordinateTupleSet a) p.val *
        (twistingTupleSectionsLinearEquiv R ι b q a x).val := by
  let e := eqToIso (coordinateTupleOpen_eq R ι q a).symm
  change (twistingSectionsLaurentAddEquiv R ι (coordinateTupleSet a) (a 0)
      ((mem_coordinateTupleSet a (a 0)).mpr ⟨0, rfl⟩) ((n : ℤ) + b)
      ((twistingSheaf R ι ((n : ℤ) + b)).val.map e.hom.op
        ((polynomialMultiplication R ι n p b).val.app
          (op (tupleOpen (coordinateOpen R ι) q a)) x))).val =
    toCoordinateLaurent R (coordinateTupleSet a) p.val *
      (twistingSectionsLaurentAddEquiv R ι (coordinateTupleSet a) (a 0)
        ((mem_coordinateTupleSet a (a 0)).mpr ⟨0, rfl⟩) b
        ((twistingSheaf R ι b).val.map e.hom.op x)).val
  rw [← PresheafOfModules.naturality_apply]
  exact polynomialMultiplication_laurent R ι n p b (coordinateTupleSet a) (a 0)
    ((mem_coordinateTupleSet a (a 0)).mpr ⟨0, rfl⟩) _

/-- The original Cech cochain map of the actual polynomial multiplication morphism. -/
def twistingCechPolynomialMap (n : ℕ) (p : homogeneousSubmodule ι R n) (b : ℤ) :
    (cechComplexFunctor (coordinateOpen R ι)).obj (twistingStructuralSections R ι b) ⟶
      (cechComplexFunctor (coordinateOpen R ι)).obj
        (twistingStructuralSections R ι ((n : ℤ) + b)) :=
  (cechComplexFunctor (coordinateOpen R ι)).map
    ((moduleSectionsPresheafFunctor (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)).map
        (polynomialMultiplication R ι n p b))

/-- Each component of the original Cech coefficient map is its actual sheaf coefficient map. -/
theorem twistingCechPolynomialMap_component (n : ℕ) (p : homogeneousSubmodule ι R n) (b : ℤ)
    (q : ℕ) (a : Fin (q + 1) → ι)
    (x : ((cechComplexFunctor (coordinateOpen R ι)).obj
      (twistingStructuralSections R ι b)).X q) :
    Pi.π (fun z : Fin (q + 1) → ι => (twistingStructuralSections R ι ((n : ℤ) + b)).obj
        (op (tupleOpen (coordinateOpen R ι) q z))) a
        ((twistingCechPolynomialMap R ι n p b).f q x) =
      (polynomialMultiplication R ι n p b).val.app (op (tupleOpen (coordinateOpen R ι) q a))
        (Pi.π (fun z : Fin (q + 1) → ι => (twistingStructuralSections R ι b).obj
          (op (tupleOpen (coordinateOpen R ι) q z))) a x) := by
  let φ := (moduleSectionsPresheafFunctor (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)).map
      (polynomialMultiplication R ι n p b)
  have h := ConcreteCategory.congr_hom (Pi.map_π
    (fun z : Fin (q + 1) → ι => φ.app (op (tupleOpen (coordinateOpen R ι) q z))) a) x
  exact h

/-- The actual Cech coefficient map is literal polynomial multiplication after the original
Laurent term isomorphisms. -/
theorem twistingCechPolynomialMap_laurent (n : ℕ) (p : homogeneousSubmodule ι R n) (b : ℤ)
    (q : ℕ) (a : Fin (q + 1) → ι)
    (x : ((cechComplexFunctor (coordinateOpen R ι)).obj
      (twistingStructuralSections R ι b)).X q) :
    ((twistingCechLaurentTermIso R ι ((n : ℤ) + b) q).hom
        ((twistingCechPolynomialMap R ι n p b).f q x) a).val =
      toCoordinateLaurent R (coordinateTupleSet a) p.val *
        ((twistingCechLaurentTermIso R ι b q).hom x a).val := by
  rw [twistingCechLaurentTermIso_hom_apply, twistingCechPolynomialMap_component,
    polynomialMultiplication_tuple, twistingCechLaurentTermIso_hom_apply]

/-- The actual polynomial coefficient map on the single native Laurent tuple model,
transported through the proved geometric chain isomorphisms. -/
def twistingLaurentPolynomialMap (n : ℕ) (p : homogeneousSubmodule ι R n) (b : ℤ) :
    coordinateLaurentTupleComplex (ι := ι) R b ⟶
      coordinateLaurentTupleComplex (ι := ι) R ((n : ℤ) + b) :=
  (twistingCechLaurentIso R ι b).inv ≫ twistingCechPolynomialMap R ι n p b ≫
    (twistingCechLaurentIso R ι ((n : ℤ) + b)).hom

/-- The transported actual coefficient morphism is the literal Laurent polynomial product
in every cochain degree, with no sign or scalar adjustment. -/
theorem twistingLaurentPolynomialMap_apply (n : ℕ) (p : homogeneousSubmodule ι R n) (b : ℤ)
    (q : ℕ) (x : coordinateLaurentTupleCochains (ι := ι) R b q) (a : Fin (q + 1) → ι) :
    ((twistingLaurentPolynomialMap R ι n p b).f q x a).val =
      toCoordinateLaurent R (coordinateTupleSet a) p.val * (x a).val := by
  change ((twistingCechLaurentTermIso R ι ((n : ℤ) + b) q).hom
    ((twistingCechPolynomialMap R ι n p b).f q
      ((twistingCechLaurentTermIso R ι b q).inv x)) a).val = _
  rw [twistingCechPolynomialMap_laurent]
  congr 1
  exact congrArg (fun z : coordinateLaurentTupleCochains (ι := ι) R b q => (z a).val)
    ((twistingCechLaurentTermIso R ι b q).toLinearEquiv.apply_symm_apply x)

end AlgebraicGeometry.Scheme.Cohomology
