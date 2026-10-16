/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Flat.Localization

/-!
The original polynomial/Laurent scheme maps, flatness, both principal-open charts, literal
projection equations and genuine coordinate unit. This owner has no spectrum imports.
-/

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Affine/PolynomialLaurent.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Selection: whole_general_prerequisite; source ranges [[1, 145]].
Actual objects, maps, universes and hypotheses are preserved.
-/

@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.PolynomialLaurent

/-- The original Laurent projection induced by the coefficient inclusion. -/
def laurentProjection (R : CommRingCat.{u}) :
    Spec (.of (LaurentPolynomial R)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom LaurentPolynomial.C)

instance instFlatLaurentProjection (R : CommRingCat.{u}) : Flat (laurentProjection R) := by
  apply Flat.SpecMap_iff.mpr
  change (algebraMap R (LaurentPolynomial R)).Flat
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

/-- The literal Laurent coordinate unit, with inverse T to the minus one. -/
def laurentCoordinateUnit (R : CommRingCat.{u}) : (LaurentPolynomial R)ˣ :=
  ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1), by
    rw [← LaurentPolynomial.T_add]; norm_num, by
    rw [← LaurentPolynomial.T_add]; norm_num⟩

/-- Its actual global section on the Laurent spectrum. -/
def laurentGlobalUnit (R : CommRingCat.{u}) : (Γ(Spec (.of (LaurentPolynomial R)), ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv.hom.toMonoidHom (laurentCoordinateUnit
    R)

/-- The affine polynomial projection induced by the coefficient inclusion. -/
def polynomialProjection (R : CommRingCat.{u}) : Spec (.of (Polynomial R)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom Polynomial.C)

instance instFlatPolynomialProjection (R : CommRingCat.{u}) : Flat (polynomialProjection R) := by
  apply Flat.SpecMap_iff.mpr
  change (algebraMap R (Polynomial R)).Flat
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

/-- The affine map induced by the usual polynomial-to-Laurent inclusion. -/
def laurentPlus (R : CommRingCat.{u}) :
    Spec (.of (LaurentPolynomial R)) ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom Polynomial.toLaurent)

instance instFlatLaurentPlus (R : CommRingCat.{u}) : Flat (laurentPlus R) := by
  apply Flat.SpecMap_iff.mpr
  change (algebraMap (Polynomial R) (LaurentPolynomial R)).Flat
  rw [RingHom.flat_algebraMap_iff]
  exact IsLocalization.flat _ (Submonoid.powers (Polynomial.X : Polynomial R))

/-- The affine map induced by polynomial inclusion followed by Laurent inversion. -/
def laurentMinus (R : CommRingCat.{u}) :
    Spec (.of (LaurentPolynomial R)) ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))

instance instFlatLaurentMinus (R : CommRingCat.{u}) : Flat (laurentMinus R) := by
  apply Flat.SpecMap_iff.mpr
  apply RingHom.Flat.comp
  · change (algebraMap (Polynomial R) (LaurentPolynomial R)).Flat
    rw [RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat _ (Submonoid.powers (Polynomial.X : Polynomial R))
  · exact RingHom.Flat.of_bijective LaurentPolynomial.invert.bijective

lemma laurentPlus_projection (R : CommRingCat.{u}) :
    laurentPlus R ≫ polynomialProjection R = laurentProjection R := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact Polynomial.toLaurent_C r

lemma laurentMinus_projection (R : CommRingCat.{u}) :
    laurentMinus R ≫ polynomialProjection R = laurentProjection R := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (congrArg LaurentPolynomial.invert (Polynomial.toLaurent_C r)).trans
    (LaurentPolynomial.invert_C r)

instance instIsOpenImmersionLaurentPlus (R : CommRingCat.{u}) : IsOpenImmersion (laurentPlus R) :=
  IsOpenImmersion.of_isLocalization (S := LaurentPolynomial R) (Polynomial.X : Polynomial R)

lemma laurentPlus_opensRange (R : CommRingCat.{u}) :
    (laurentPlus R).opensRange = PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) := by
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range (LaurentPolynomial R) (Polynomial.X : Polynomial
    R)

instance instIsOpenImmersionLaurentMinus (R : CommRingCat.{u}) : IsOpenImmersion (laurentMinus R) :=
  by
  let e : CommRingCat.of (LaurentPolynomial R) ≅ CommRingCat.of (LaurentPolynomial R) :=
    (LaurentPolynomial.invert (R := R)).toRingEquiv.toCommRingCatIso
  unfold laurentMinus
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  change IsOpenImmersion (Spec.map e.hom ≫ laurentPlus R)
  infer_instance

lemma laurentMinus_opensRange (R : CommRingCat.{u}) :
    (laurentMinus R).opensRange = PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) := by
  let e : CommRingCat.of (LaurentPolynomial R) ≅ CommRingCat.of (LaurentPolynomial R) :=
    (LaurentPolynomial.invert (R := R)).toRingEquiv.toCommRingCatIso
  have he : laurentMinus R = Spec.map e.hom ≫ laurentPlus R := by
    unfold laurentMinus
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  simpa only [he] using
    (Scheme.Hom.opensRange_comp_of_isIso (Spec.map e.hom) (laurentPlus R)).trans
      (laurentPlus_opensRange R)


lemma laurentGlobalUnit_original_T (R : CommRingCat.{u}) :
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom (↑(laurentGlobalUnit R)) =
      LaurentPolynomial.T 1 := by
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (LaurentPolynomial.T 1)) = _
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv_hom_id _


end AlgebraicGeometry.Scheme.PolynomialLaurent
