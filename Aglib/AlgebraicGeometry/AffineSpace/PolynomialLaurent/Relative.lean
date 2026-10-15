/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Products.IntegerBase
public import Aglib.AlgebraicGeometry.AffineSpace.PolynomialLaurent.Basic

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/PolynomialLaurent.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 99]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
The genuine relative polynomial/Laurent schemes on arbitrary qc bases, their actual coordinate open
immersions, flat projections and exact natural projection triangles. Morphisms of the qc base
category are unrestricted.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

open AlgebraicGeometry.Scheme.Products

namespace AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

/-- The universe-lifted integer ring used as the common base for Bass products. -/
abbrev integerRing : CommRingCat.{u} := .of (ULift.{u} ℤ)

/-- The actual relative affine line X × Spec(Z[t]). -/
def polynomialFunctor : QuasiCompactSchemes.{u} ⥤ QuasiCompactSchemes.{u} :=
  qcBaseProductFunctor (PolynomialLaurent.polynomialProjection integerRing)

/-- The actual relative Laurent scheme X × Spec(Z[t,t⁻¹]). -/
def laurentFunctor : QuasiCompactSchemes.{u} ⥤ QuasiCompactSchemes.{u} :=
  qcBaseProductFunctor (PolynomialLaurent.laurentProjection integerRing)

/-- The original plus-coordinate open chart, base changed over the actual integral base. -/
def plus : laurentFunctor.{u} ⟶ polynomialFunctor.{u} :=
  qcBaseProductTransformation _ _ (PolynomialLaurent.laurentPlus integerRing)
    (PolynomialLaurent.laurentPlus_projection integerRing)

/-- The original inverse-coordinate open chart, with no choice of local coordinates on X. -/
def minus : laurentFunctor.{u} ⟶ polynomialFunctor.{u} :=
  qcBaseProductTransformation _ _ (PolynomialLaurent.laurentMinus integerRing)
    (PolynomialLaurent.laurentMinus_projection integerRing)

instance instIsOpenImmersionPlus (X : QuasiCompactSchemes.{u}) : IsOpenImmersion (plus.app X).hom :=
  by
  exact instIsOpenImmersionBaseProductTransformation _ _ _
    (PolynomialLaurent.laurentPlus_projection integerRing) X.obj

instance instIsOpenImmersionMinus (X : QuasiCompactSchemes.{u}) : IsOpenImmersion (minus.app X).hom
  :=
  by
  exact instIsOpenImmersionBaseProductTransformation _ _ _
    (PolynomialLaurent.laurentMinus_projection integerRing) X.obj

/-- The original relative affine-line projection. -/
def polynomialProjection : polynomialFunctor.{u} ⟶ 𝟭 _ where
  app X := ⟨(baseProductProjection _).app X.obj⟩
  naturality {X Y} f := by
    apply ObjectProperty.hom_ext
    exact (baseProductProjection _).naturality f.hom

/-- The original relative Laurent projection. -/
def laurentProjection : laurentFunctor.{u} ⟶ 𝟭 _ where
  app X := ⟨(baseProductProjection _).app X.obj⟩
  naturality {X Y} f := by
    apply ObjectProperty.hom_ext
    exact (baseProductProjection _).naturality f.hom

instance instFlatPolynomialProjection (X : QuasiCompactSchemes.{u}) :
    Flat (polynomialProjection.app X).hom := by
  change Flat (pullback.fst (toIntegerBase X.obj) (PolynomialLaurent.polynomialProjection
    integerRing))
  infer_instance

instance instFlatLaurentProjection (X : QuasiCompactSchemes.{u}) :
    Flat (laurentProjection.app X).hom := by
  change Flat (pullback.fst (toIntegerBase X.obj) (PolynomialLaurent.laurentProjection integerRing))
  infer_instance

@[reassoc (attr := simp)] lemma plus_projection (X : QuasiCompactSchemes.{u}) :
    plus.app X ≫ polynomialProjection.app X = laurentProjection.app X := by
  apply ObjectProperty.hom_ext
  exact baseProductTransformation_projection _ _ _
    (PolynomialLaurent.laurentPlus_projection integerRing) X.obj

@[reassoc (attr := simp)] lemma minus_projection (X : QuasiCompactSchemes.{u}) :
    minus.app X ≫ polynomialProjection.app X = laurentProjection.app X := by
  apply ObjectProperty.hom_ext
  exact baseProductTransformation_projection _ _ _
    (PolynomialLaurent.laurentMinus_projection integerRing) X.obj


end AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

end
