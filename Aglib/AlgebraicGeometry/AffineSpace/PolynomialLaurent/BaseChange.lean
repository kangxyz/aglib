/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Aglib.AlgebraicGeometry.AffineSpace.PolynomialLaurent.Relative
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Affine/PolynomialLaurentBaseChange.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 148]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
Genuine affine identifications of the relative polynomial and Laurent base products. Both original
projections, all ring-map naturality squares and the plus/inverse-coordinate chart maps are
preserved. This owner is independent of spectra and K-groups.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

open AlgebraicGeometry.Scheme.Products

namespace AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

/-- The actual initial integral coefficient map. -/
def integerMap (R : CommRingCat.{u}) : integerRing ⟶ R := CommRingCat.isInitial.to R

@[simp] lemma spec_integerMap (R : CommRingCat.{u}) :
    Spec.map (integerMap R) = toIntegerBase (Spec R) := specULiftZIsTerminal.hom_ext _ _

/-- The direct affine polynomial model gives the genuine base-product pullback square. -/
lemma polynomialSpec_isPullback (R : CommRingCat.{u}) :
    IsPullback (PolynomialLaurent.polynomialProjection R)
      (Spec.map (CommRingCat.PolynomialLaurent.polynomialMap (integerMap R)))
      (toIntegerBase (Spec R)) (PolynomialLaurent.polynomialProjection integerRing) := by
  have h := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.PolynomialLaurent.polynomial_isPushout (integerMap R))
  simpa only [spec_integerMap, CommRingCat.PolynomialLaurent.coefficient,
    PolynomialLaurent.polynomialProjection] using h

/-- The direct affine Laurent model gives the genuine base-product pullback square. -/
lemma laurentSpec_isPullback (R : CommRingCat.{u}) :
    IsPullback (PolynomialLaurent.laurentProjection R)
      (Spec.map (CommRingCat.PolynomialLaurent.laurentMap (integerMap R)))
      (toIntegerBase (Spec R)) (PolynomialLaurent.laurentProjection integerRing) := by
  have h := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.PolynomialLaurent.laurent_isPushout (integerMap R))
  simpa only [spec_integerMap, CommRingCat.PolynomialLaurent.laurentCoefficient,
    PolynomialLaurent.laurentProjection] using h

/-- The actual polynomial affine-to-product isomorphism. -/
def polynomialSpecIso (R : CommRingCat.{u}) :
    Spec (.of (Polynomial R)) ≅
      (baseProductFunctor (PolynomialLaurent.polynomialProjection integerRing)).obj (Spec R) :=
  (polynomialSpec_isPullback R).isoPullback

/-- The actual Laurent affine-to-product isomorphism. -/
def laurentSpecIso (R : CommRingCat.{u}) :
    Spec (.of (LaurentPolynomial R)) ≅
      (baseProductFunctor (PolynomialLaurent.laurentProjection integerRing)).obj (Spec R) :=
  (laurentSpec_isPullback R).isoPullback

@[reassoc (attr := simp)] lemma polynomialSpecIso_hom_fst (R : CommRingCat.{u}) :
    (polynomialSpecIso R).hom ≫ pullback.fst _ _ = PolynomialLaurent.polynomialProjection R :=
  (polynomialSpec_isPullback R).isoPullback_hom_fst

@[reassoc (attr := simp)] lemma polynomialSpecIso_hom_snd (R : CommRingCat.{u}) :
    (polynomialSpecIso R).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.PolynomialLaurent.polynomialMap (integerMap R)) :=
  (polynomialSpec_isPullback R).isoPullback_hom_snd

@[reassoc (attr := simp)] lemma laurentSpecIso_hom_fst (R : CommRingCat.{u}) :
    (laurentSpecIso R).hom ≫ pullback.fst _ _ = PolynomialLaurent.laurentProjection R :=
  (laurentSpec_isPullback R).isoPullback_hom_fst

@[reassoc (attr := simp)] lemma laurentSpecIso_hom_snd (R : CommRingCat.{u}) :
    (laurentSpecIso R).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.PolynomialLaurent.laurentMap (integerMap R)) :=
  (laurentSpec_isPullback R).isoPullback_hom_snd

@[simp, reassoc] lemma integerMap_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    integerMap R ≫ f = integerMap S := CommRingCat.isInitial.hom_ext _ _

/-- Naturality of the original polynomial product isomorphism on every ring map. -/
@[reassoc] lemma polynomialSpecIso_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Spec.map (CommRingCat.PolynomialLaurent.polynomialMap f) ≫ (polynomialSpecIso R).hom =
      (polynomialSpecIso S).hom ≫
        (baseProductFunctor (PolynomialLaurent.polynomialProjection integerRing)).map (Spec.map f)
          := by
  apply pullback.hom_ext
  · simp only [Category.assoc,polynomialSpecIso_hom_fst,baseProductFunctor,
      pullback.lift_fst,polynomialSpecIso_hom_fst_assoc]
    rw [PolynomialLaurent.polynomialProjection,PolynomialLaurent.polynomialProjection,←
      Spec.map_comp,← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.PolynomialLaurent.polynomial_square f).symm
  · simp only [Category.assoc,polynomialSpecIso_hom_snd,baseProductFunctor,
      pullback.lift_snd,Category.comp_id,← Spec.map_comp]
    rw [← CommRingCat.PolynomialLaurent.polynomialMap_comp,integerMap_naturality]

/-- Naturality of the original Laurent product isomorphism on every ring map. -/
@[reassoc] lemma laurentSpecIso_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Spec.map (CommRingCat.PolynomialLaurent.laurentMap f) ≫ (laurentSpecIso R).hom =
      (laurentSpecIso S).hom ≫
        (baseProductFunctor (PolynomialLaurent.laurentProjection integerRing)).map (Spec.map f) :=
          by
  apply pullback.hom_ext
  · simp only [Category.assoc,laurentSpecIso_hom_fst,baseProductFunctor,
      pullback.lift_fst,laurentSpecIso_hom_fst_assoc]
    rw [PolynomialLaurent.laurentProjection,PolynomialLaurent.laurentProjection,← Spec.map_comp,←
      Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.PolynomialLaurent.laurent_square f).symm
  · simp only [Category.assoc,laurentSpecIso_hom_snd,baseProductFunctor,
      pullback.lift_snd,Category.comp_id,← Spec.map_comp]
    rw [← CommRingCat.PolynomialLaurent.laurentMap_comp,integerMap_naturality]

/-- The plus chart is preserved by the original affine/product identifications. -/
@[reassoc] lemma polynomialLaurentSpecIso_plus (R : CommRingCat.{u}) :
    PolynomialLaurent.laurentPlus R ≫ (polynomialSpecIso R).hom =
      (laurentSpecIso R).hom ≫
        (baseProductTransformation _ _ (PolynomialLaurent.laurentPlus integerRing)
          (PolynomialLaurent.laurentPlus_projection integerRing)).app (Spec R) := by
  apply pullback.hom_ext
  · simp [baseProductTransformation,PolynomialLaurent.laurentPlus_projection]
  · simp only [Category.assoc,polynomialSpecIso_hom_snd,baseProductTransformation,
      pullback.lift_snd,laurentSpecIso_hom_snd_assoc]
    rw [PolynomialLaurent.laurentPlus,PolynomialLaurent.laurentPlus,← Spec.map_comp,← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.PolynomialLaurent.toLaurent_naturality (integerMap R))

/-- The inverse chart is preserved as well, including its actual Laurent inversion. -/
@[reassoc] lemma polynomialLaurentSpecIso_minus (R : CommRingCat.{u}) :
    PolynomialLaurent.laurentMinus R ≫ (polynomialSpecIso R).hom =
      (laurentSpecIso R).hom ≫
        (baseProductTransformation _ _ (PolynomialLaurent.laurentMinus integerRing)
          (PolynomialLaurent.laurentMinus_projection integerRing)).app (Spec R) := by
  apply pullback.hom_ext
  · simp [baseProductTransformation,PolynomialLaurent.laurentMinus_projection]
  · simp only [Category.assoc,polynomialSpecIso_hom_snd,baseProductTransformation,
      pullback.lift_snd,laurentSpecIso_hom_snd_assoc]
    rw [PolynomialLaurent.laurentMinus,PolynomialLaurent.laurentMinus,← Spec.map_comp,←
      Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.PolynomialLaurent.minus_naturality (integerMap R))

end AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

end
