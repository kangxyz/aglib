/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Map
public import Aglib.AlgebraicGeometry.ProjectiveSpace.CoordinateRing

/-!
# The original homogeneous chart maps under coefficient change

The chart ring map is the native homogeneous-localization map of the original
graded coefficient homomorphism. It preserves the original coefficients and
coordinate ratios, and its spectrum map is exactly the chart of `Proj.map`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The native homogeneous-localization map on the original coordinate chart ring. -/
def coordinateRingMap (f : R →+* S) (ι : Type u) (i : ι) :
    coordinateRing R ι i →+* coordinateRing S ι i :=
  HomogeneousLocalization.map (MvPolynomial.gradedMap f)
    (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩)

/-- The original chart map applies the original coefficient homomorphism to the numerator. -/
theorem coordinateRingMap_mk (f : R →+* S) (ι : Type u) (i : ι) (n : ℕ)
    (p : MvPolynomial ι R) (hp : p ∈ MvPolynomial.homogeneousSubmodule ι R (n • 1)) :
    coordinateRingMap f ι i
        (Away.mk (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.isHomogeneous_X R i)
          n p hp) =
      Away.mk (MvPolynomial.homogeneousSubmodule ι S) (MvPolynomial.isHomogeneous_X S i)
        n (MvPolynomial.map f p) (hp.map f) := by
  apply HomogeneousLocalization.val_injective
  simp [coordinateRingMap, Away.mk, HomogeneousLocalization.map_mk]

@[simp]
theorem coordinateRingMap_coefficient (f : R →+* S) (ι : Type u) (i : ι) (r : R) :
    coordinateRingMap f ι i (coordinateRingCoefficient R ι i r) =
      coordinateRingCoefficient S ι i (f r) := by
  change coordinateRingMap f ι i
    (Away.mk (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.isHomogeneous_X R i)
      0 (MvPolynomial.C r) (MvPolynomial.isHomogeneous_C ι r)) = _
  rw [coordinateRingMap_mk]
  simp only [MvPolynomial.map_C]
  rfl

@[simp]
theorem coordinateRingMap_ratio (f : R →+* S) (ι : Type u) (i j : ι) :
    coordinateRingMap f ι i (coordinateRatio R ι i j) = coordinateRatio S ι i j := by
  simp only [coordinateRatio, coordinateRingMap_mk, MvPolynomial.map_X]

/-- The native chart map agrees with polynomial coefficient change on the original chart
generators. -/
theorem coordinateRingMap_comp_polynomialToCoordinateRing (f : R →+* S) (ι : Type u)
    (i : ι) :
    (coordinateRingMap f ι i).comp (polynomialToCoordinateRing R ι i) =
      (polynomialToCoordinateRing S ι i).comp (MvPolynomial.map f) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro j
    simp

/-- The original coordinate-ring equivalences intertwine the native chart map with the
original polynomial coefficient homomorphism. -/
theorem coordinateRingEquivPolynomial_map (f : R →+* S) (ι : Type u) (i : ι) :
    (coordinateRingEquivPolynomial S ι i).toRingHom.comp (coordinateRingMap f ι i) =
      (MvPolynomial.map f).comp (coordinateRingEquivPolynomial R ι i).toRingHom := by
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := (coordinateRingEquivPolynomial R ι i).symm.surjective z
  have hp : coordinateRingMap f ι i ((coordinateRingEquivPolynomial R ι i).symm p) =
      (coordinateRingEquivPolynomial S ι i).symm (MvPolynomial.map f p) :=
    RingHom.congr_fun (coordinateRingMap_comp_polynomialToCoordinateRing f ι i) p
  change (coordinateRingEquivPolynomial S ι i)
      (coordinateRingMap f ι i ((coordinateRingEquivPolynomial R ι i).symm p)) =
    MvPolynomial.map f ((coordinateRingEquivPolynomial R ι i)
      ((coordinateRingEquivPolynomial R ι i).symm p))
  rw [hp, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/-- On the original affine chart, the projective coefficient morphism is the spectrum of
the original homogeneous-localization map. -/
@[reassoc]
theorem coordinateRingMap_awayι (f : R →+* S) (ι : Type u) (i : ι) :
    Proj.awayι (MvPolynomial.homogeneousSubmodule ι S) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X S i) Nat.zero_lt_one ≫ map f ι =
      Spec.map (CommRingCat.ofHom (coordinateRingMap f ι i)) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one := by
  have H (x : MvPolynomial ι S) (hx : x = MvPolynomial.gradedMap f (MvPolynomial.X i))
      (hd : x ∈ MvPolynomial.homogeneousSubmodule ι S 1) :
      Proj.awayι (MvPolynomial.homogeneousSubmodule ι S) x hd Nat.zero_lt_one ≫ map f ι =
        Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.map (MvPolynomial.gradedMap f)
            (P := Submonoid.powers (MvPolynomial.X (R := R) i)) (Q := Submonoid.powers x)
            (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp [hx]⟩))) ≫
          Proj.awayι (MvPolynomial.homogeneousSubmodule ι R) (MvPolynomial.X i)
            (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one := by
    subst x
    exact Proj.awayι_comp_map (MvPolynomial.gradedMap (ι := ι) f)
      (MvPolynomial.irrelevant_map_gradedMap f).ge Nat.zero_lt_one
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X R i)
  exact H (MvPolynomial.X i) (by simp) (MvPolynomial.isHomogeneous_X S i)

/-- The original projective coefficient morphism lies over the original spectrum map. -/
@[reassoc (attr := simp)]
theorem map_toSpec (f : R →+* S) (ι : Type u) :
    map f ι ≫ toSpec R ι = toSpec S ι ≫ Spec.map (CommRingCat.ofHom f) := by
  apply (coordinateAffineOpenCover S ι).openCover.hom_ext
  intro i
  change Proj.awayι (MvPolynomial.homogeneousSubmodule ι S) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X S i) Nat.zero_lt_one ≫ (map f ι ≫ toSpec R ι) =
    Proj.awayι (MvPolynomial.homogeneousSubmodule ι S) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X S i) Nat.zero_lt_one ≫
        (toSpec S ι ≫ Spec.map (CommRingCat.ofHom f))
  rw [coordinateRingMap_awayι_assoc, coordinateChart_toSpec, coordinateChart_toSpec_assoc]
  change Spec.map (CommRingCat.ofHom (coordinateRingMap f ι i)) ≫
      Spec.map (CommRingCat.ofHom (coordinateRingCoefficient R ι i)) =
    Spec.map (CommRingCat.ofHom (coordinateRingCoefficient S ι i)) ≫
      Spec.map (CommRingCat.ofHom f)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact coordinateRingMap_coefficient f ι i r

end AlgebraicGeometry.ProjectiveSpace
