/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.Square
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
Source: `Quillen/Algebra/Polynomial/LaurentUnderSquare.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 133]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# The original Laurent square over one fixed coefficient ring

Polynomial and Laurent extension preserve the actual structure map from a fixed ring R. The
positive and inverse-coordinate legs therefore form the original strict square in Under R,
not merely after forgetting to rings. This is the coefficient diagram used with fixed original
open-pair pullbacks; no algebra is replaced and no comparison square is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace CommRingCat.PolynomialLaurent
variable (R : CommRingCat.{u})

/-- Original polynomial extension as an endofunctor of the fixed ring's algebra category. -/
def polynomialUnderFunctor : Under R ⥤ Under R where
  obj a := Under.mk (a.hom ≫ coefficient a.right)
  map {a b} f := Under.homMk (polynomialMap f.right) (by
    change (a.hom ≫ coefficient a.right) ≫ polynomialMap f.right = b.hom ≫ coefficient b.right
    rw [Category.assoc, ← polynomial_square, ← Category.assoc, Under.w])
  map_id a := by apply Under.UnderMorphism.ext; exact polynomialMap_id a.right
  map_comp f g := by apply Under.UnderMorphism.ext; exact polynomialMap_comp f.right g.right

/-- Original Laurent extension retains the same fixed coefficient ring. -/
def laurentUnderFunctor : Under R ⥤ Under R where
  obj a := Under.mk (a.hom ≫ laurentCoefficient a.right)
  map {a b} f := Under.homMk (laurentMap f.right) (by
    change (a.hom ≫ laurentCoefficient a.right) ≫ laurentMap f.right =
      b.hom ≫ laurentCoefficient b.right
    rw [Category.assoc, ← laurent_square, ← Category.assoc, Under.w])
  map_id a := by apply Under.UnderMorphism.ext; exact laurentMap_id a.right
  map_comp f g := by apply Under.UnderMorphism.ext; exact laurentMap_comp f.right g.right

/-- The original polynomial coefficient inclusion is a natural algebra arrow. -/
def polynomialUnderCoefficient : 𝟭 (Under R) ⟶ polynomialUnderFunctor R where
  app a := Under.homMk (coefficient a.right) rfl
  naturality _ _ f := by apply Under.UnderMorphism.ext; exact polynomial_square f.right

/-- The original Laurent coefficient inclusion is likewise a natural algebra arrow. -/
def laurentUnderCoefficient : 𝟭 (Under R) ⟶ laurentUnderFunctor R where
  app a := Under.homMk (laurentCoefficient a.right) rfl
  naturality _ _ f := by apply Under.UnderMorphism.ext; exact laurent_square f.right

/-- The positive-coordinate Laurent leg retains the original fixed-base structure equation. -/
def underToLaurent : polynomialUnderFunctor R ⟶ laurentUnderFunctor R where
  app a := Under.homMk (CommRingCat.ofHom (Polynomial.toLaurent (R := a.right))) (by
    change (a.hom ≫ coefficient a.right) ≫ CommRingCat.ofHom Polynomial.toLaurent =
      a.hom ≫ laurentCoefficient a.right
    rw [Category.assoc, coefficient_toLaurent])
  naturality _ _ f := by apply Under.UnderMorphism.ext; exact toLaurent_naturality f.right

/-- The inverse-coordinate Laurent leg retains its original structure equation. -/
def underToLaurentInvert : polynomialUnderFunctor R ⟶ laurentUnderFunctor R where
  app a := Under.homMk (CommRingCat.ofHom
    ((LaurentPolynomial.invert (R := a.right)).toRingHom.comp Polynomial.toLaurent)) (by
      change (a.hom ≫ coefficient a.right) ≫ CommRingCat.ofHom
        (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent) =
          a.hom ≫ laurentCoefficient a.right
      rw [Category.assoc, coefficient_toLaurent_invert])
  naturality _ _ f := by apply Under.UnderMorphism.ext; exact minus_naturality f.right

/-- The original positive leg has the actual original Laurent coefficient composite. -/
theorem polynomialUnderCoefficient_toLaurent (a : Under R) :
    (polynomialUnderCoefficient R).app a ≫ (underToLaurent R).app a =
      (laurentUnderCoefficient R).app a := by
  apply Under.UnderMorphism.ext
  exact coefficient_toLaurent a.right

/-- The inverse-coordinate leg has the very same original Laurent coefficient composite. -/
theorem polynomialUnderCoefficient_toLaurentInvert (a : Under R) :
    (polynomialUnderCoefficient R).app a ≫ (underToLaurentInvert R).app a =
      (laurentUnderCoefficient R).app a := by
  apply Under.UnderMorphism.ext
  exact coefficient_toLaurent_invert a.right

/-- The original polynomial/Laurent square as an actual square over the fixed base ring. -/
def laurentUnderSquare (a : Under R) : Arrow (Arrow (Under R)) :=
  Arrow.mk (Arrow.homMk (f := Arrow.mk ((polynomialUnderCoefficient R).app a))
    (g := Arrow.mk ((underToLaurentInvert R).app a))
    ((polynomialUnderCoefficient R).app a) ((underToLaurent R).app a) (by
      exact (polynomialUnderCoefficient_toLaurentInvert R a).trans
        (polynomialUnderCoefficient_toLaurent R a).symm))

/-- All four original coefficient maps preserve this fixed-base square. -/
def laurentUnderSquareMap {a b : Under R} (f : a ⟶ b) :
    laurentUnderSquare R a ⟶ laurentUnderSquare R b :=
  Arrow.homMk
    (Arrow.homMk f ((polynomialUnderFunctor R).map f)
      ((polynomialUnderCoefficient R).naturality f))
    (Arrow.homMk ((polynomialUnderFunctor R).map f) ((laurentUnderFunctor R).map f)
      ((underToLaurentInvert R).naturality f)) (by
        apply Arrow.hom_ext
        · exact (polynomialUnderCoefficient R).naturality f
        · exact (underToLaurent R).naturality f)

/-- The unchanged square is strictly functorial on original coefficient algebras. -/
def laurentUnderSquareFunctor : Under R ⥤ Arrow (Arrow (Under R)) where
  obj := laurentUnderSquare R
  map := laurentUnderSquareMap R
  map_id a := by
    apply Arrow.hom_ext
    · apply Arrow.hom_ext
      · rfl
      · exact (polynomialUnderFunctor R).map_id a
    · apply Arrow.hom_ext
      · exact (polynomialUnderFunctor R).map_id a
      · exact (laurentUnderFunctor R).map_id a
  map_comp f g := by
    apply Arrow.hom_ext
    · apply Arrow.hom_ext
      · rfl
      · exact (polynomialUnderFunctor R).map_comp f g
    · apply Arrow.hom_ext
      · exact (polynomialUnderFunctor R).map_comp f g
      · exact (laurentUnderFunctor R).map_comp f g

/-- Forgetting the algebra structure retains the original Laurent ring square literally. -/
theorem laurentUnderSquare_forget (a : Under R) :
    (Under.forget R).mapArrow.mapArrow.obj (laurentUnderSquare R a) =
      laurentSquare a.right := rfl

end CommRingCat.PolynomialLaurent
