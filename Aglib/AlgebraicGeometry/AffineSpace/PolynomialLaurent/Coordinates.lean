/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.AffineSpace.PolynomialLaurent.Basic

/-!
# Actual global polynomial coordinates on the Laurent charts

The affine global-sections isomorphism identifies the polynomial variable with the
Laurent unit on the positive chart and its inverse on the negative chart. All maps
are the original scheme maps, over arbitrary commutative rings including the zero ring.

Source: archive Quillen/AlgebraicGeometry/Scheme/Affine/PolynomialCoordinate.lean
SHA256: 49eef11c2a0faa65f158a3d3bd52e42ec88f24658f08970459f57ecb40e5c6f8
Selection: lines 23-49, the actual polynomial coordinate and positive-chart equation.
Source: archive Quillen/AlgebraicGeometry/Scheme/Affine/LaurentNegativeCoordinate.lean
SHA256: e8e5d4b2a82cc5978f3863a16bfa435ac976d258264cc7824c05ca4a290b1667
Selection: lines 25-51, the actual negative-chart coordinate equation.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.PolynomialLaurent

/-- The literal polynomial variable as an original global section of the polynomial spectrum. -/
def polynomialGlobalCoordinate (R : CommRingCat.{u}) : Γ(Spec (.of (Polynomial R)), ⊤) :=
  (Scheme.ΓSpecIso (.of (Polynomial R))).inv (Polynomial.X : Polynomial R)

/-- Original affine global sections identify this coordinate with the unchanged polynomial X. -/
theorem polynomialGlobalCoordinate_original (R : CommRingCat.{u}) :
    (Scheme.ΓSpecIso (.of (Polynomial R))).hom (polynomialGlobalCoordinate R) =
      (Polynomial.X : Polynomial R) := by
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of (Polynomial R))).inv_hom_id _

/-- On the original positive Laurent open, X is exactly the existing Laurent global unit T. -/
theorem polynomialGlobalCoordinate_laurentPlus (R : CommRingCat.{u}) :
    (laurentPlus R).appTop (polynomialGlobalCoordinate R) = ↑(laurentGlobalUnit R) := by
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom).injective
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Polynomial.toLaurent (R := R))))
    (polynomialGlobalCoordinate R)
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom
    ((laurentPlus R).appTop (polynomialGlobalCoordinate R)) =
      Polynomial.toLaurent ((Scheme.ΓSpecIso (.of (Polynomial R))).hom
        (polynomialGlobalCoordinate R)) at h
  rw [polynomialGlobalCoordinate_original, Polynomial.toLaurent_X] at h
  rw [laurentGlobalUnit_original_T]
  exact h


/-- The original negative chart sends its polynomial coordinate to the inverse Laurent unit. -/
theorem polynomialGlobalCoordinate_laurentMinus (R : CommRingCat.{u}) :
    (laurentMinus R).appTop (polynomialGlobalCoordinate R) =
      ↑((laurentGlobalUnit R)⁻¹) := by
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom).injective
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
      (LaurentPolynomial.invert.toRingHom.comp (Polynomial.toLaurent (R := R)))))
    (polynomialGlobalCoordinate R)
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom
    ((laurentMinus R).appTop (polynomialGlobalCoordinate R)) =
      LaurentPolynomial.invert (Polynomial.toLaurent
        ((Scheme.ΓSpecIso (.of (Polynomial R))).hom
          (polynomialGlobalCoordinate R))) at h
  rw [polynomialGlobalCoordinate_original, Polynomial.toLaurent_X,
    LaurentPolynomial.invert_T] at h
  have hi : (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom
      (↑((laurentGlobalUnit R)⁻¹)) = LaurentPolynomial.T (-1) := by
    change (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (LaurentPolynomial.T (-1))) = _
    exact ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv_hom_id _
  rw [hi]
  exact h

end AlgebraicGeometry.Scheme.PolynomialLaurent
