/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Finite towers of the original polynomial projection

The native polynomial equivalences identify the zero-variable projection with
an isomorphism and factor each successor-variable projection through the
existing one-variable `polynomialProjection`. The factorization is an equality
of the actual spectrum maps. The same one-variable projection is smooth of
relative dimension one over every commutative ring.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

variable (R : CommRingCat.{u}) (n : ℕ)

/-- The native zero-variable polynomial equivalence on the actual spectra. -/
def mvPolynomialZeroIso : Spec (.of (MvPolynomial (Fin 0) R)) ≅ Spec R :=
  Scheme.Spec.mapIso
    (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingEquiv.toCommRingCatIso.symm.op

/-- The zero-variable isomorphism has precisely the original structural map. -/
@[simp]
theorem mvPolynomialZeroIso_hom :
    (mvPolynomialZeroIso R).hom =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin 0) R)) := by
  change Spec.map (CommRingCat.ofHom
    (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm.toRingHom) = _
  rw [MvPolynomial.isEmptyAlgEquiv_symm_toRingHom]

instance mvPolynomialProjection_zero_isIso :
    IsIso (Spec.map
      (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin 0) R))) := by
  rw [← mvPolynomialZeroIso_hom R]
  infer_instance

/-- The actual successor-variable affine spectrum is the polynomial line over
the spectrum with one fewer variable. -/
def mvPolynomialSuccIso :
    Spec (.of (MvPolynomial (Fin (n + 1)) R)) ≅
      Spec (.of (Polynomial (MvPolynomial (Fin n) R))) :=
  Scheme.Spec.mapIso (MvPolynomial.finSuccEquiv R n).toRingEquiv.toCommRingCatIso.symm.op

@[simp]
theorem mvPolynomialSuccIso_hom :
    (mvPolynomialSuccIso R n).hom =
      Spec.map (CommRingCat.ofHom (MvPolynomial.finSuccEquiv R n).symm.toRingHom) := rfl

/-- The exact successor projection factors through the existing one-variable
projection, not a replacement structural map. -/
@[reassoc]
theorem mvPolynomialSuccIso_projection :
    (mvPolynomialSuccIso R n).hom ≫
        polynomialProjection (.of (MvPolynomial (Fin n) R)) ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)) =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : R →+* MvPolynomial (Fin (n + 1)) R)) := by
  rw [mvPolynomialSuccIso_hom, polynomialProjection,
    ← Spec.map_comp_assoc, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact DFunLike.congr_fun (MvPolynomial.finSuccEquiv_comp_C_eq_C (R := R) n) r

/-- The original affine polynomial projection is a smooth relative curve over
an arbitrary commutative base ring. -/
instance polynomialProjection_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 1 (polynomialProjection R) := by
  let : Algebra.IsStandardSmoothOfRelativeDimension 1 R (MvPolynomial PUnit.{u+1} R) := by
    simpa using Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial R PUnit.{u+1}
  let : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Polynomial R) :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
      (MvPolynomial.uniqueAlgEquiv R PUnit.{u+1})
  change SmoothOfRelativeDimension 1
    (Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R))))
  apply HasRingHomProperty.Spec_iff.mpr
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr inferInstance

instance polynomialProjection_smooth : Smooth (polynomialProjection R) :=
  SmoothOfRelativeDimension.smooth 1 (polynomialProjection R)

end AlgebraicGeometry.Scheme.PolynomialLaurent
