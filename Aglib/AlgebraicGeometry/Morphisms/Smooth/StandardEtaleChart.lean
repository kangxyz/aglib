/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Aglib.AlgebraicGeometry.Morphisms.Etale.StalkMap
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Standard-smooth algebras and their actual etale charts

Source: `lean/R5Lab/Aglib/AlgebraicGeometry/Morphisms/Smooth/StandardEtaleChart.lean`.
Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `2b600da31050ed86661e9f169b83d6f2640d64c92851aa5c4ee17ba6bed7cd8b`.
Native objects and proved suppliers replace application provenance and redundant premises.
-/

@[expose] public section


noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u


namespace AlgebraicGeometry.Scheme.StandardSmoothEtaleChart
variable (n : ℕ) (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.IsStandardSmoothOfRelativeDimension n R A]

/-- An actual coordinate map supplied by the proved standard-smooth theorem. -/
def coordinateMap : MvPolynomial (Fin n) R →ₐ[R] A :=
  Classical.choose (Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n R A)

lemma coordinateMap_etale : (coordinateMap n R A).toRingHom.Etale :=
  Classical.choose_spec
    (Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n R A)

/-- Actual etale map from the same affine scheme to polynomial affine space. -/
def polynomialChart : Spec (.of A) ⟶ Spec (.of (MvPolynomial (Fin n) R)) :=
  Spec.map (CommRingCat.ofHom (coordinateMap n R A).toRingHom)

instance polynomialChart_etale : Etale (polynomialChart n R A) :=
  HasRingHomProperty.Spec_iff.mpr (coordinateMap_etale n R A)

@[reassoc] lemma polynomialChart_structure :
    polynomialChart n R A ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [polynomialChart, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (coordinateMap n R A).comp_algebraMap

include n in
/-- The native actual-stalk theorem supplies regularity of the chosen etale chart. -/
lemma regularStalks [IsRegularRing R] :
    Scheme.RegularStalks (Spec (.of A)) := by
  intro x
  let : IsRegularLocalRing
      ((Spec (.of (MvPolynomial (Fin n) R))).presheaf.stalk (polynomialChart n R A x)) :=
    Scheme.regularStalks_spec (MvPolynomial (Fin n) R) _
  exact Scheme.isRegularLocalRing_stalk_of_etale (polynomialChart n R A) x

end AlgebraicGeometry.Scheme.StandardSmoothEtaleChart
