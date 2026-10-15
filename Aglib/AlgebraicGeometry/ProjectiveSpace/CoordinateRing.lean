/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Aglib.RingTheory.MvPolynomial.Homogeneous

/-!
# Polynomial coordinates on the standard projective charts

The degree-zero localization at `Xᵢ` has coordinate functions `Xⱼ / Xᵢ`.
Dehomogenization substitutes `1` for `Xᵢ` and leaves all other coordinates free.
The constructions use the native homogeneous localization and its canonical map to localization.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory MvPolynomial HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The native degree-zero homogeneous localization on a standard projective chart. -/
abbrev coordinateRing (i : ι) :=
  HomogeneousLocalization.Away (homogeneousSubmodule ι R) (X i)

/-- The inclusion of base coefficients into the native projective chart ring. -/
def coordinateRingCoefficient (i : ι) : R →+* coordinateRing R ι i :=
  (fromZeroRingHom (homogeneousSubmodule ι R) (Submonoid.powers (X i))).comp
    (toHomogeneousSubmoduleZero R ι)

/-- The homogeneous fraction `Xⱼ / Xᵢ` in the chart where `Xᵢ` does not vanish. -/
def coordinateRatio (i j : ι) : coordinateRing R ι i :=
  Away.mk (homogeneousSubmodule ι R) (isHomogeneous_X R i) 1 (X j)
    (by simpa using isHomogeneous_X R j)

@[simp]
theorem coordinateRatio_self (i : ι) : coordinateRatio R ι i i = 1 := by
  apply HomogeneousLocalization.val_injective
  simp [coordinateRatio]

/-- Dehomogenization at `i`, keeping the coordinates different from `i` as independent variables. -/
def dehomogenize (i : ι) : MvPolynomial ι R →+* MvPolynomial {j : ι // j ≠ i} R := by
  classical
  exact eval₂Hom C (fun j => if h : j = i then 1 else X ⟨j, h⟩)

@[simp]
theorem dehomogenize_C (i : ι) (r : R) : dehomogenize R ι i (C r) = C r := by
  classical
  simp [dehomogenize]

@[simp]
theorem dehomogenize_X_self (i : ι) : dehomogenize R ι i (X i) = 1 := by
  classical
  simp [dehomogenize]

@[simp]
theorem dehomogenize_X_ne (i : ι) (j : {j : ι // j ≠ i}) :
    dehomogenize R ι i (X j.1) = X j := by
  classical
  simp [dehomogenize, j.2]

/-- Evaluation at `Xᵢ = 1` on the actual homogeneous localization. -/
def coordinateRingToPolynomial (i : ι) :
    coordinateRing R ι i →+* MvPolynomial {j : ι // j ≠ i} R :=
  (Localization.awayLift (dehomogenize R ι i) (X i) (by simp)).comp
    (algebraMap (coordinateRing R ι i) (Localization.Away (X (R := R) i)))

/-- A homogeneous fraction is dehomogenized by evaluating its numerator at `Xᵢ = 1`. -/
theorem coordinateRingToPolynomial_mk (i : ι) (n : ℕ) (p : MvPolynomial ι R)
    (hp : p ∈ homogeneousSubmodule ι R (n • 1)) :
    coordinateRingToPolynomial R ι i
      (Away.mk (homogeneousSubmodule ι R) (isHomogeneous_X R i) n p hp) =
        dehomogenize R ι i p := by
  change Localization.awayLift (dehomogenize R ι i) (X i) (by simp)
    (Localization.mk p ⟨X i ^ n, n, rfl⟩) = _
  simpa using Localization.awayLift_mk (dehomogenize R ι i) (X i) p 1 (by simp) n

@[simp]
theorem coordinateRingToPolynomial_coefficient (i : ι) (r : R) :
    coordinateRingToPolynomial R ι i (coordinateRingCoefficient R ι i r) = C r := by
  change coordinateRingToPolynomial R ι i
    (Away.mk (homogeneousSubmodule ι R) (isHomogeneous_X R i) 0 (C r)
      (isHomogeneous_C ι r)) = C r
  rw [coordinateRingToPolynomial_mk, dehomogenize_C]

@[simp]
theorem coordinateRingToPolynomial_ratio (i : ι) (j : {j : ι // j ≠ i}) :
    coordinateRingToPolynomial R ι i (coordinateRatio R ι i j.1) = X j := by
  rw [coordinateRatio, coordinateRingToPolynomial_mk, dehomogenize_X_ne]

/-- The map from affine polynomial coordinates to the fractions `Xⱼ / Xᵢ`. -/
def polynomialToCoordinateRing (i : ι) :
    MvPolynomial {j : ι // j ≠ i} R →+* coordinateRing R ι i :=
  eval₂Hom (coordinateRingCoefficient R ι i) (fun j => coordinateRatio R ι i j.1)

@[simp]
theorem polynomialToCoordinateRing_C (i : ι) (r : R) :
    polynomialToCoordinateRing R ι i (C r) = coordinateRingCoefficient R ι i r := by
  simp [polynomialToCoordinateRing]

@[simp]
theorem polynomialToCoordinateRing_X (i : ι) (j : {j : ι // j ≠ i}) :
    polynomialToCoordinateRing R ι i (X j) = coordinateRatio R ι i j.1 := by
  simp [polynomialToCoordinateRing]

/-- Dehomogenizing after substitution of the chart ratios fixes every polynomial coordinate. -/
theorem coordinateRingToPolynomial_comp_polynomialToCoordinateRing (i : ι) :
    (coordinateRingToPolynomial R ι i).comp (polynomialToCoordinateRing R ι i) =
      RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro j
    simp

@[simp]
theorem val_coordinateRingCoefficient (i : ι) (r : R) :
    (coordinateRingCoefficient R ι i r).val =
      algebraMap (MvPolynomial ι R) (Localization.Away (X (R := R) i)) (C r) := rfl

/-- The chart ratio has its usual value in the ambient polynomial localization. -/
theorem val_coordinateRatio (i j : ι) :
    (coordinateRatio R ι i j).val =
      IsLocalization.Away.invSelf (S := Localization.Away (X (R := R) i)) (X (R := R) i) *
        algebraMap (MvPolynomial ι R) (Localization.Away (X (R := R) i)) (X j) := by
  change (Localization.mk (X (R := R) j) ⟨X i ^ 1, 1, rfl⟩ :
    Localization.Away (X (R := R) i)) = _
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  simpa only [pow_one, IsLocalization.Away.invSelf] using
    mul_comm (algebraMap (MvPolynomial ι R) (Localization.Away (X (R := R) i)) (X j))
      (IsLocalization.mk' (Localization.Away (X (R := R) i)) 1 ⟨X i, Submonoid.mem_powers _⟩)

private theorem val_polynomialToCoordinateRing_dehomogenize (i : ι)
    (p : MvPolynomial ι R) :
    (polynomialToCoordinateRing R ι i (dehomogenize R ι i p)).val =
      p.eval₂ ((algebraMap (MvPolynomial ι R) (Localization.Away (X (R := R) i))).comp C)
        (fun j =>
          IsLocalization.Away.invSelf (S := Localization.Away (X (R := R) i)) (X (R := R) i) *
          algebraMap (MvPolynomial ι R) (Localization.Away (X (R := R) i)) (X j)) := by
  have h : ((algebraMap (coordinateRing R ι i) (Localization.Away (X (R := R) i))).comp
      (polynomialToCoordinateRing R ι i)).comp (dehomogenize R ι i) =
        eval₂Hom ((algebraMap (MvPolynomial ι R) (Localization.Away (X (R := R) i))).comp C)
          (fun j =>
          IsLocalization.Away.invSelf (S := Localization.Away (X (R := R) i)) (X (R := R) i) *
            algebraMap (MvPolynomial ι R) (Localization.Away (X (R := R) i)) (X j)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro j
      simp only [RingHom.comp_apply, eval₂Hom_X', HomogeneousLocalization.algebraMap_apply]
      by_cases hji : j = i
      · subst j
        simp only [dehomogenize_X_self, map_one, HomogeneousLocalization.val_one]
        simpa only [mul_comm] using (IsLocalization.Away.mul_invSelf
          (S := Localization.Away (X (R := R) i)) (X (R := R) i)).symm
      · rw [dehomogenize_X_ne R ι i ⟨j, hji⟩, polynomialToCoordinateRing_X,
          val_coordinateRatio]
  exact RingHom.congr_fun h p

/-- Substituting the chart ratios into the dehomogenization of a degree-`n` polynomial recovers
its homogeneous fraction with denominator `Xᵢ ^ n`. -/
theorem polynomialToCoordinateRing_dehomogenize (i : ι) (n : ℕ) (p : MvPolynomial ι R)
    (hp : p ∈ homogeneousSubmodule ι R (n • 1)) :
    polynomialToCoordinateRing R ι i (dehomogenize R ι i p) =
      Away.mk (homogeneousSubmodule ι R) (isHomogeneous_X R i) n p hp := by
  apply HomogeneousLocalization.val_injective
  rw [val_polynomialToCoordinateRing_dehomogenize, Away.val_mk]
  have hp' : p.IsHomogeneous n := by simpa using hp
  rw [hp'.eval₂_mul, ← MvPolynomial.hom_eval₂, eval₂_eta,
    Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
  simp only [map_pow]
  calc
    _ = algebraMap (MvPolynomial ι R) (Localization.Away (X (R := R) i)) p *
        (algebraMap (MvPolynomial ι R) (Localization.Away (X (R := R) i)) (X (R := R) i) *
          IsLocalization.Away.invSelf
            (S := Localization.Away (X (R := R) i)) (X (R := R) i)) ^ n := by
            rw [mul_pow]
            ac_rfl
    _ = _ := by simp

/-- The chart ratios and dehomogenization are inverse on the actual degree-zero localization. -/
theorem polynomialToCoordinateRing_comp_coordinateRingToPolynomial (i : ι) :
    (polynomialToCoordinateRing R ι i).comp (coordinateRingToPolynomial R ι i) =
      RingHom.id _ := by
  apply RingHom.ext
  intro z
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective (homogeneousSubmodule ι R) (isHomogeneous_X R i) z
  simpa only [RingHom.comp_apply, RingHom.id_apply, coordinateRingToPolynomial_mk] using
    polynomialToCoordinateRing_dehomogenize R ι i n p hp

/-- The native degree-zero projective chart ring is a polynomial ring in the other coordinates. -/
def coordinateRingEquivPolynomial (i : ι) :
    coordinateRing R ι i ≃+* MvPolynomial {j : ι // j ≠ i} R where
  __ := coordinateRingToPolynomial R ι i
  invFun := polynomialToCoordinateRing R ι i
  left_inv z := RingHom.congr_fun
    (polynomialToCoordinateRing_comp_coordinateRingToPolynomial R ι i) z
  right_inv p := RingHom.congr_fun
    (coordinateRingToPolynomial_comp_polynomialToCoordinateRing R ι i) p

/-- The standard coordinate open of polynomial projective space is the affine polynomial scheme
in the remaining coordinates. -/
def coordinateOpenIsoSpecPolynomial (i : ι) :
    (coordinateOpen R ι i).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial {j : ι // j ≠ i} R)) :=
  Proj.basicOpenIsoSpec (homogeneousSubmodule ι R) (X i) (isHomogeneous_X R i)
    Nat.zero_lt_one ≪≫
      Scheme.Spec.mapIso (coordinateRingEquivPolynomial R ι i).toCommRingCatIso.symm.op

end AlgebraicGeometry.ProjectiveSpace
