/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.CoordinateRing
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Projective zero-space over its original base

For a singleton coordinate type, the sole coordinate chart is the whole
projective scheme. Its native homogeneous-localization coefficient map is a
ring isomorphism, because its polynomial chart has no remaining variables.
Consequently the original structure morphism is an isomorphism over every
commutative ring, including the zero ring. The `PUnit` specialization stays in
the universe of the base ring and supplies projective zero-space.
-/

@[expose] public section

noncomputable section

open CategoryTheory MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The only coordinate open is the whole projective scheme. -/
theorem coordinateOpen_eq_top_of_subsingleton [Subsingleton ι] (i : ι) :
    coordinateOpen R ι i = ⊤ := by
  apply le_antisymm le_top
  rw [← iSup_coordinateOpen_eq_top R ι]
  exact iSup_le fun j => by rw [Subsingleton.elim j i]

/-- A singleton-coordinate chart has its original base ring as coordinate ring. -/
def coordinateRingEquivBase [Subsingleton ι] (i : ι) :
    coordinateRing R ι i ≃+* R := by
  have : IsEmpty {j : ι // j ≠ i} := ⟨fun j => j.2 (Subsingleton.elim _ _)⟩
  exact (coordinateRingEquivPolynomial R ι i).trans
    (MvPolynomial.isEmptyAlgEquiv R {j : ι // j ≠ i}).toRingEquiv

/-- The singleton-chart equivalence retains the original coefficient map. -/
@[simp]
theorem coordinateRingEquivBase_coefficient [Subsingleton ι] (i : ι) (r : R) :
    coordinateRingEquivBase R ι i (coordinateRingCoefficient R ι i r) = r := by
  have : IsEmpty {j : ι // j ≠ i} := ⟨fun j => j.2 (Subsingleton.elim _ _)⟩
  change (MvPolynomial.isEmptyAlgEquiv R {j : ι // j ≠ i})
    (coordinateRingToPolynomial R ι i (coordinateRingCoefficient R ι i r)) = r
  rw [coordinateRingToPolynomial_coefficient]
  exact (MvPolynomial.isEmptyAlgEquiv R {j : ι // j ≠ i}).commutes r

/-- With one homogeneous coordinate, the original structure morphism is an isomorphism. -/
instance instIsIsoToSpecOfUnique [Unique ι] : IsIso (toSpec R ι) := by
  let i : ι := default
  have hc : (coordinateRingEquivBase R ι i).symm.toRingHom =
      coordinateRingCoefficient R ι i := by
    apply RingHom.ext
    intro r
    apply (coordinateRingEquivBase R ι i).injective
    change (coordinateRingEquivBase R ι i) ((coordinateRingEquivBase R ι i).symm r) = _
    rw [RingEquiv.apply_symm_apply, coordinateRingEquivBase_coefficient]
  have : IsIso (CommRingCat.ofHom (coordinateRingCoefficient R ι i)) := by
    rw [← hc]
    change IsIso (coordinateRingEquivBase R ι i).toCommRingCatIso.inv
    infer_instance
  have hi : IsIso (coordinateOpen R ι i).ι := by
    rw [coordinateOpen_eq_top_of_subsingleton R ι i, ← Scheme.topIso_hom]
    infer_instance
  have : IsIso (Proj.awayι (homogeneousSubmodule ι R) (X i)
      (isHomogeneous_X R i) Nat.zero_lt_one) := by
    change IsIso ((Proj.basicOpenIsoSpec (homogeneousSubmodule ι R) (X i)
      (isHomogeneous_X R i) Nat.zero_lt_one).inv ≫ (coordinateOpen R ι i).ι)
    exact IsIso.comp_isIso' (Iso.isIso_inv _) hi
  have : IsIso (Proj.awayι (homogeneousSubmodule ι R) (X i)
      (isHomogeneous_X R i) Nat.zero_lt_one ≫ toSpec R ι) := by
    rw [coordinateChart_toSpec]
    change IsIso (Spec.map (CommRingCat.ofHom (coordinateRingCoefficient R ι i)))
    infer_instance
  exact IsIso.of_isIso_comp_left
    (Proj.awayι (homogeneousSubmodule ι R) (X i) (isHomogeneous_X R i) Nat.zero_lt_one)
    (toSpec R ι)

/-- Projective zero-space is the spectrum of the original base ring. -/
def pointIsoSpec : ProjectiveSpace R PUnit.{u + 1} ≅ Spec (CommRingCat.of R) :=
  asIso (toSpec R PUnit.{u + 1})

/-- The forward map is exactly the original projective structure morphism. -/
@[simp]
theorem pointIsoSpec_hom : (pointIsoSpec R).hom = toSpec R PUnit.{u + 1} := rfl

end AlgebraicGeometry.ProjectiveSpace
