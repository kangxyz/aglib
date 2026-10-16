/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.CoordinateRing
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Logic.Equiv.Option

/-!
# Finite-type affine schemes in actual standard projective charts

A finite polynomial presentation gives an original surjective map from the degree-zero
homogeneous-localization chart ring. Its native Spec map is a closed immersion into the
standard chart and hence an immersion into the original polynomial Proj. The structural
factorization is the literal original Spec map. No Noetherian or field hypothesis is used.
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

variable (R : Type u) [CommRing R]

/-- The original chart at the distinguished `none` coordinate, with its remaining coordinates
reindexed by the original polynomial-presentation variables. -/
def optionCoordinateRingEquivPolynomial (I : Type u) :
    coordinateRing R (Option I) none ≃+* MvPolynomial I R := by
  classical
  exact (coordinateRingEquivPolynomial R (Option I) none).trans
    (MvPolynomial.renameEquiv R
      ((Equiv.optionSubtype (α := I) (β := Option I) none)
        ⟨Equiv.refl _, rfl⟩).symm).toRingEquiv

/-- This reindexing keeps the original structural coefficients exactly. -/
theorem optionCoordinateRingEquivPolynomial_coefficient (I : Type u) (r : R) :
    optionCoordinateRingEquivPolynomial R I (coordinateRingCoefficient R (Option I) none r) =
      C r := by
  classical
  change (MvPolynomial.renameEquiv R
    ((Equiv.optionSubtype (α := I) (β := Option I) none) ⟨Equiv.refl _, rfl⟩).symm)
      (coordinateRingToPolynomial R (Option I) none
        (coordinateRingCoefficient R (Option I) none r)) = C r
  rw [coordinateRingToPolynomial_coefficient]
  simp

variable (A : Type u) [CommRing A] [Algebra R A] (I : Type u)
  (p : MvPolynomial I R →ₐ[R] A)

/-- The original presentation map expressed on the actual projective chart ring. -/
def affinePresentationChartRingHom : coordinateRing R (Option I) none →+* A :=
  p.toRingHom.comp (optionCoordinateRingEquivPolynomial R I).toRingHom

/-- The actual chart-ring presentation preserves the original base-ring map. -/
theorem affinePresentationChartRingHom_coefficient (r : R) :
    affinePresentationChartRingHom R A I p (coordinateRingCoefficient R (Option I) none r) =
      algebraMap R A r := by
  change p (optionCoordinateRingEquivPolynomial R I
    (coordinateRingCoefficient R (Option I) none r)) = _
  rw [optionCoordinateRingEquivPolynomial_coefficient]
  exact p.commutes r

/-- Surjectivity is that of the original presentation followed by the original chart equivalence. -/
theorem affinePresentationChartRingHom_surjective (hp : Function.Surjective p) :
    Function.Surjective (affinePresentationChartRingHom R A I p) :=
  hp.comp (optionCoordinateRingEquivPolynomial R I).surjective

/-- The actual Spec presentation maps into the distinguished standard open. -/
def affinePresentationChartMap : Spec (CommRingCat.of A) ⟶
    (coordinateOpen R (Option I) none).toScheme :=
  Spec.map (CommRingCat.ofHom (affinePresentationChartRingHom R A I p)) ≫
    (Proj.basicOpenIsoSpec (homogeneousSubmodule (Option I) R) (X none)
      (isHomogeneous_X R none) Nat.zero_lt_one).inv

/-- The original finite-presentation map into the original polynomial projective space. -/
def affinePresentationImmersion : Spec (CommRingCat.of A) ⟶ ProjectiveSpace R (Option I) :=
  affinePresentationChartMap R A I p ≫ (coordinateOpen R (Option I) none).ι

/-- The original immersion also factors through the native homogeneous-localization chart map. -/
theorem affinePresentationImmersion_eq :
    affinePresentationImmersion R A I p =
      Spec.map (CommRingCat.ofHom (affinePresentationChartRingHom R A I p)) ≫
        Proj.awayι (homogeneousSubmodule (Option I) R) (X none)
          (isHomogeneous_X R none) Nat.zero_lt_one := by
  rw [affinePresentationImmersion, affinePresentationChartMap, Category.assoc]
  rfl

/-- A surjective original polynomial presentation is closed in the actual standard chart. -/
theorem affinePresentationChartMap_isClosedImmersion (hp : Function.Surjective p) :
    IsClosedImmersion (affinePresentationChartMap R A I p) := by
  let : IsClosedImmersion (Spec.map
      (CommRingCat.ofHom (affinePresentationChartRingHom R A I p))) :=
    IsClosedImmersion.spec_of_surjective _ (affinePresentationChartRingHom_surjective R A I p hp)
  unfold affinePresentationChartMap
  infer_instance

/-- The resulting original projective-space map is an actual immersion. -/
theorem affinePresentationImmersion_isImmersion (hp : Function.Surjective p) :
    IsImmersion (affinePresentationImmersion R A I p) := by
  let := affinePresentationChartMap_isClosedImmersion R A I p hp
  unfold affinePresentationImmersion
  infer_instance

/-- The original structural map is preserved exactly by the actual projective immersion. -/
@[reassoc]
theorem affinePresentationImmersion_toSpec :
    affinePresentationImmersion R A I p ≫ toSpec R (Option I) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  have hc : CommRingCat.ofHom (coordinateRingCoefficient R (Option I) none) ≫
      CommRingCat.ofHom (affinePresentationChartRingHom R A I p) =
        CommRingCat.ofHom (algebraMap R A) := by
    ext r
    exact affinePresentationChartRingHom_coefficient R A I p r
  rw [affinePresentationImmersion_eq, Category.assoc, coordinateChart_toSpec]
  change Spec.map (CommRingCat.ofHom (affinePresentationChartRingHom R A I p)) ≫
    Spec.map (CommRingCat.ofHom (coordinateRingCoefficient R (Option I) none)) = _
  rw [← Spec.map_comp, hc]

variable {R A}

omit [Algebra R A] in
/-- Every original finite-type ring map gives a closed immersion of its spectrum into an
actual standard chart of finite polynomial projective space, over the original ring map. -/
theorem exists_projectiveChart_closedImmersion_of_finiteType
    (φ : R →+* A) (hφ : φ.FiniteType) :
    ∃ (I : Type u) (_ : Fintype I)
      (j : Spec (CommRingCat.of A) ⟶ (coordinateOpen R (Option I) none).toScheme),
      IsClosedImmersion j ∧
        (j ≫ (coordinateOpen R (Option I) none).ι) ≫ toSpec R (Option I) =
          Spec.map (CommRingCat.ofHom φ) := by
  let : Algebra R A := φ.toAlgebra
  obtain ⟨I, hI, p, hp⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial' (R := R) (S := A)).mp hφ
  exact ⟨I, hI, affinePresentationChartMap R A I p,
    affinePresentationChartMap_isClosedImmersion R A I p hp,
    affinePresentationImmersion_toSpec R A I p⟩

omit [Algebra R A] in
/-- An arbitrary finite-type affine ring map admits an actual immersion into finite
polynomial projective space, with exactly its original structural factorization. -/
theorem exists_projectiveImmersion_of_finiteType (φ : R →+* A) (hφ : φ.FiniteType) :
    ∃ (I : Type u) (_ : Fintype I)
      (j : Spec (CommRingCat.of A) ⟶ ProjectiveSpace R (Option I)),
      IsImmersion j ∧ j ≫ toSpec R (Option I) = Spec.map (CommRingCat.ofHom φ) := by
  obtain ⟨I, hI, j, hj, hcomp⟩ := exists_projectiveChart_closedImmersion_of_finiteType φ hφ
  let := hI
  let := hj
  exact ⟨I, hI, j ≫ (coordinateOpen R (Option I) none).ι, inferInstance, hcomp⟩

end AlgebraicGeometry.ProjectiveSpace
