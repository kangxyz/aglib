/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
Source: `Quillen/Algebra/Polynomial/LaurentSquare.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 96]]. Actual objects, maps and hypotheses are preserved.
-/

/-! The literal polynomial and Laurent coefficient square as a strict ring-valued diagram. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace CommRingCat.PolynomialLaurent

@[simp] theorem polynomialMap_id (R : CommRingCat.{u}) :
    polynomialMap (𝟙 R) = 𝟙 (CommRingCat.of (Polynomial R)) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact Polynomial.map_id

@[simp] theorem laurentMap_id (R : CommRingCat.{u}) :
    laurentMap (𝟙 R) = 𝟙 (CommRingCat.of (LaurentPolynomial R)) := by
  apply CommRingCat.hom_ext
  apply laurent_hom_ext
  · intro r
    exact laurentMap_C (𝟙 R) r
  · exact laurentMap_T (𝟙 R) 1

/-- The two original polynomial charts, with positive and inverse Laurent coordinates. -/
def laurentSquare (R : CommRingCat.{u}) : Arrow (Arrow CommRingCat.{u}) :=
  Arrow.mk (Arrow.homMk (f := Arrow.mk (coefficient R))
    (g := Arrow.mk (CommRingCat.ofHom
      (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)))
    (coefficient R) (CommRingCat.ofHom Polynomial.toLaurent) (by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      change LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.C r)) =
        Polynomial.toLaurent (Polynomial.C r)
      rw [Polynomial.toLaurent_C, LaurentPolynomial.invert_C]))

/-- All four coefficient maps give a literal map between the original commuting squares. -/
def laurentSquareMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    laurentSquare R ⟶ laurentSquare S :=
  Arrow.homMk
    (Arrow.homMk f (polynomialMap f) (polynomial_square f))
    (Arrow.homMk (polynomialMap f) (laurentMap f) (minus_naturality f)) (by
      apply Arrow.hom_ext
      · exact polynomial_square f
      · exact toLaurent_naturality f)

/-- The actual Bass evaluation square is strictly functorial in the coefficient ring. -/
def laurentSquareFunctor : CommRingCat.{u} ⥤ Arrow (Arrow CommRingCat.{u}) where
  obj := laurentSquare
  map := laurentSquareMap
  map_id R := by
    apply Arrow.hom_ext
    · apply Arrow.hom_ext
      · rfl
      · exact polynomialMap_id R
    · apply Arrow.hom_ext
      · exact polynomialMap_id R
      · exact laurentMap_id R
  map_comp f g := by
    apply Arrow.hom_ext
    · apply Arrow.hom_ext
      · rfl
      · exact polynomialMap_comp f g
    · apply Arrow.hom_ext
      · exact polynomialMap_comp f g
      · exact laurentMap_comp f g

/-- The original positive Laurent leg sends polynomial coefficients to Laurent coefficients. -/
theorem coefficient_toLaurent (R : CommRingCat.{u}) :
    coefficient R ≫ CommRingCat.ofHom Polynomial.toLaurent = laurentCoefficient R := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact Polynomial.toLaurent_C r

/-- The original inverse-coordinate Laurent leg has the same literal coefficient inclusion. -/
theorem coefficient_toLaurent_invert (R : CommRingCat.{u}) :
    coefficient R ≫
      CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent) =
        laurentCoefficient R := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (congrArg LaurentPolynomial.invert (Polynomial.toLaurent_C r)).trans
    (LaurentPolynomial.invert_C r)

end CommRingCat.PolynomialLaurent
