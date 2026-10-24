/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Basic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Geometric fibers of the original polynomial projection

The existing `polynomialProjection` has geometrically integral, and hence
geometrically connected, fibers over every commutative ring. The proof uses
the native affine-space projection and the exact polynomial spectrum
isomorphism. No field, Noetherian, or properness hypothesis is imposed on
the original base.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

variable (R : CommRingCat.{u})

/-- The original polynomial projection has geometrically integral fibers over
an arbitrary commutative base ring. -/
instance polynomialProjection_geometricallyIntegral :
    GeometricallyIntegral (polynomialProjection R) := by
  have : MorphismProperty.RespectsIso (@GeometricallyIntegral.{u}) := by
    rw [GeometricallyIntegral.eq_geometrically]
    infer_instance
  change GeometricallyIntegral (Spec.algebraMap R (Polynomial R))
  let e := Scheme.Spec.mapIso (MvPolynomial.uniqueAlgEquiv R
    PUnit.{u+1}).toRingEquiv.toCommRingCatIso.op
  have hm : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial PUnit.{u+1} R)))) := by
    change GeometricallyIntegral (Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : R →+* MvPolynomial PUnit.{u+1} R)))
    rw [← AffineSpace.SpecIso_inv_over (n := PUnit.{u+1}) R]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := fun {X Y : Scheme.{u}} (f : X ⟶ Y) => GeometricallyIntegral f) _ _).mpr
        inferInstance
  have he : e.hom ≫ Spec.map
      (CommRingCat.ofHom (algebraMap R (MvPolynomial PUnit.{u+1} R))) =
        Spec.algebraMap R (Polynomial R) :=
    Spec.map_algHom_algebraMap (MvPolynomial.uniqueAlgEquiv R PUnit.{u+1}).toAlgHom
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := fun {X Y : Scheme.{u}} (f : X ⟶ Y) => GeometricallyIntegral f) _ _).mpr hm

/-- Every actual field-valued base change of the same polynomial projection
is connected. -/
instance polynomialProjection_geometricallyConnected :
    GeometricallyConnected (polynomialProjection R) := by
  constructor
  intro K _ y Z fst snd h
  have : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
  infer_instance

end AlgebraicGeometry.Scheme.PolynomialLaurent
