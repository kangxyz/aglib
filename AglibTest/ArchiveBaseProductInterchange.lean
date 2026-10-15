/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineSpace.PolynomialLaurent.ProductInterchange
public import Aglib.AlgebraicGeometry.AffineSpace.PolynomialLaurent.Coordinates
public import Mathlib.Data.ZMod.Basic

/-! # Strict clients of actual integer-base product interchange and chart coordinates -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Products
  AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
universe u
namespace AglibTest.ArchiveBaseProductInterchange

variable {S T S' T' : AlgebraicGeometry.Scheme.{u}}

/-- The shared original base is fixed as an equality of actual projection maps. -/
theorem original_shared_coordinate (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductSwapIso p q).hom.app X ≫
        pullback.fst (toIntegerBase ((baseProductFunctor q).obj X)) p ≫
          pullback.fst (toIntegerBase X) q =
      pullback.fst (toIntegerBase ((baseProductFunctor p).obj X)) q ≫
        pullback.fst (toIntegerBase X) p :=
  baseProductSwapMap_fst_fst p q X

/-- Both independent fixed-factor coordinates are retained in their exact swapped positions. -/
theorem original_factor_coordinates (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    (X : AlgebraicGeometry.Scheme.{u}) :
    ((baseProductSwapIso p q).hom.app X ≫
        pullback.fst (toIntegerBase ((baseProductFunctor q).obj X)) p ≫
          pullback.snd (toIntegerBase X) q =
      pullback.snd (toIntegerBase ((baseProductFunctor p).obj X)) q) ∧
    ((baseProductSwapIso p q).hom.app X ≫
        pullback.snd (toIntegerBase ((baseProductFunctor q).obj X)) p =
      pullback.fst (toIntegerBase ((baseProductFunctor p).obj X)) q ≫
        pullback.snd (toIntegerBase X) p) :=
  ⟨baseProductSwapMap_fst_snd p q X, baseProductSwapMap_snd p q X⟩

/-- The two actual selected swap maps cancel, rather than identifying their objects. -/
theorem original_swap_involution (p : S ⟶ integerBase) (q : T ⟶ integerBase) :
    baseProductSwapIso p q ≪≫ baseProductSwapIso q p = Iso.refl _ :=
  baseProductSwapIso_trans p q

/-- Every base arrow is allowed, without a flatness or quasi-compactness hypothesis. -/
theorem arbitrary_original_base_map (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    (baseProductFunctor q).map ((baseProductFunctor p).map f) ≫
        (baseProductSwapIso p q).hom.app Y =
      (baseProductSwapIso p q).hom.app X ≫
        (baseProductFunctor p).map ((baseProductFunctor q).map f) :=
  baseProductSwapMap_naturality p q f

/-- Both original projection squares hold for the same complete swap. -/
theorem original_projection_squares (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    (X : AlgebraicGeometry.Scheme.{u}) :
    ((baseProductSwapIso p q).hom.app X ≫
        (baseProductProjection p).app ((baseProductFunctor q).obj X) =
      (baseProductFunctor q).map ((baseProductProjection p).app X)) ∧
    ((baseProductSwapIso p q).hom.app X ≫
        (baseProductFunctor p).map ((baseProductProjection q).app X) =
      (baseProductProjection q).app ((baseProductFunctor p).obj X)) :=
  ⟨baseProductSwapIso_projection_first p q X, baseProductSwapIso_projection_second p q X⟩

/-- The first fixed factor is changed by its actual original map over the integral base. -/
theorem original_first_factor_map (p : S ⟶ integerBase) (p' : S' ⟶ integerBase)
    (q : T ⟶ integerBase) (f : S ⟶ S') (hf : f ≫ p' = p)
    (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductFunctor q).map ((baseProductTransformation p p' f hf).app X) ≫
        (baseProductSwapIso p' q).hom.app X =
      (baseProductSwapIso p q).hom.app X ≫
        (baseProductTransformation p p' f hf).app ((baseProductFunctor q).obj X) :=
  baseProductSwapIso_transformation_first p p' q f hf X

/-- The second fixed factor has its own independent original map and square. -/
theorem original_second_factor_map (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    (q' : T' ⟶ integerBase) (g : T ⟶ T') (hg : g ≫ q' = q)
    (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductTransformation q q' g hg).app ((baseProductFunctor p).obj X) ≫
        (baseProductSwapIso p q').hom.app X =
      (baseProductSwapIso p q).hom.app X ≫
        (baseProductFunctor p).map ((baseProductTransformation q q' g hg).app X) :=
  baseProductSwapIso_transformation_second p q q' g hg X

/-- The quasi-compact lift uses the unchanged underlying scheme morphism. -/
theorem original_qc_underlying_map (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    [QuasiCompact p] [QuasiCompact q] (X : QuasiCompactSchemes.{u}) :
    ((qcBaseProductSwapIso p q).hom.app X).hom = (baseProductSwapIso p q).hom.app X.obj :=
  qcBaseProductSwapIso_hom_hom p q X

/-- The first positive chart commutes with an independent actual Laurent factor. -/
theorem original_plus_first_laurent (X : QuasiCompactSchemes.{u}) :
    laurentFunctor.map (plus.app X) ≫
        (qcBaseProductSwapIso (PolynomialLaurent.polynomialProjection integerRing)
          (PolynomialLaurent.laurentProjection integerRing)).hom.app X =
      (qcBaseProductSwapIso (PolynomialLaurent.laurentProjection integerRing)
        (PolynomialLaurent.laurentProjection integerRing)).hom.app X ≫
          plus.app (laurentFunctor.obj X) :=
  qcBaseProductSwapIso_plus_first _ X

/-- The first inverse chart commutes with an independent actual polynomial factor. -/
theorem original_minus_first_polynomial (X : QuasiCompactSchemes.{u}) :
    polynomialFunctor.map (minus.app X) ≫
        (qcBaseProductSwapIso (PolynomialLaurent.polynomialProjection integerRing)
          (PolynomialLaurent.polynomialProjection integerRing)).hom.app X =
      (qcBaseProductSwapIso (PolynomialLaurent.laurentProjection integerRing)
        (PolynomialLaurent.polynomialProjection integerRing)).hom.app X ≫
          minus.app (polynomialFunctor.obj X) :=
  qcBaseProductSwapIso_minus_first _ X

/-- The second positive chart retains the opposite placement in the actual product square. -/
theorem original_plus_second_polynomial (X : QuasiCompactSchemes.{u}) :
    plus.app (polynomialFunctor.obj X) ≫
        (qcBaseProductSwapIso (PolynomialLaurent.polynomialProjection integerRing)
          (PolynomialLaurent.polynomialProjection integerRing)).hom.app X =
      (qcBaseProductSwapIso (PolynomialLaurent.polynomialProjection integerRing)
        (PolynomialLaurent.laurentProjection integerRing)).hom.app X ≫
          polynomialFunctor.map (plus.app X) :=
  qcBaseProductSwapIso_plus_second _ X

/-- The second inverse chart retains the original Laurent inversion and independent variable. -/
theorem original_minus_second_laurent (X : QuasiCompactSchemes.{u}) :
    minus.app (laurentFunctor.obj X) ≫
        (qcBaseProductSwapIso (PolynomialLaurent.laurentProjection integerRing)
          (PolynomialLaurent.polynomialProjection integerRing)).hom.app X =
      (qcBaseProductSwapIso (PolynomialLaurent.laurentProjection integerRing)
        (PolynomialLaurent.laurentProjection integerRing)).hom.app X ≫
          laurentFunctor.map (minus.app X) :=
  qcBaseProductSwapIso_minus_second _ X

/-- Even two polynomial factors retain distinct coordinates rather than an identity swap. -/
theorem original_two_polynomial_coordinates (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductSwapIso (PolynomialLaurent.polynomialProjection integerRing)
        (PolynomialLaurent.polynomialProjection integerRing)).hom.app X ≫
      pullback.snd
        (toIntegerBase ((baseProductFunctor
          (PolynomialLaurent.polynomialProjection integerRing)).obj X))
        (PolynomialLaurent.polynomialProjection integerRing) =
      pullback.fst
        (toIntegerBase ((baseProductFunctor
          (PolynomialLaurent.polynomialProjection integerRing)).obj X))
        (PolynomialLaurent.polynomialProjection integerRing) ≫
          pullback.snd (toIntegerBase X) (PolynomialLaurent.polynomialProjection integerRing) :=
  baseProductSwapMap_snd _ _ X

/-- Two Laurent factors likewise retain both original independent coordinate maps. -/
theorem original_two_laurent_coordinates (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductSwapIso (PolynomialLaurent.laurentProjection integerRing)
        (PolynomialLaurent.laurentProjection integerRing)).hom.app X ≫
      pullback.fst
        (toIntegerBase ((baseProductFunctor
          (PolynomialLaurent.laurentProjection integerRing)).obj X))
        (PolynomialLaurent.laurentProjection integerRing) ≫
          pullback.snd (toIntegerBase X) (PolynomialLaurent.laurentProjection integerRing) =
      pullback.snd
        (toIntegerBase ((baseProductFunctor
          (PolynomialLaurent.laurentProjection integerRing)).obj X))
        (PolynomialLaurent.laurentProjection integerRing) :=
  baseProductSwapMap_fst_snd _ _ X

/-- The two actual chart coordinates have opposite Laurent orientations. -/
theorem chart_coordinates_mul (R : CommRingCat.{u}) :
    (PolynomialLaurent.laurentPlus R).appTop (PolynomialLaurent.polynomialGlobalCoordinate R) *
      (PolynomialLaurent.laurentMinus R).appTop (PolynomialLaurent.polynomialGlobalCoordinate R) =
        1 := by
  rw [PolynomialLaurent.polynomialGlobalCoordinate_laurentPlus,
    PolynomialLaurent.polynomialGlobalCoordinate_laurentMinus]
  exact Units.mul_inv (PolynomialLaurent.laurentGlobalUnit R)

/-- The same actual coordinate equation includes the zero ring. -/
private theorem zero_ring_chart_coordinates_mul :
    (PolynomialLaurent.laurentPlus (.of (ZMod 1))).appTop
        (PolynomialLaurent.polynomialGlobalCoordinate (.of (ZMod 1))) *
      (PolynomialLaurent.laurentMinus (.of (ZMod 1))).appTop
        (PolynomialLaurent.polynomialGlobalCoordinate (.of (ZMod 1))) = 1 :=
  chart_coordinates_mul _

end AglibTest.ArchiveBaseProductInterchange
