/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.PolynomialLaurentNaturality

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/CoefficientPolynomialLaurentSchemeNaturality.lean` at
LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 93]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Original native polynomial and Laurent products under scheme restriction

The existing native product comparisons and both original chart maps commute
with every scheme-over-base arrow on the fixed coefficient fibers. The proofs
use the actual joint pullback maps and their two projections. No compactness,
flatness or separation assumption is needed. These geometric squares do not
assert naturality of an assembled negative-group or telescope comparison.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
universe u

open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

namespace AlgebraicGeometry.Scheme.BaseChange.Coefficients
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)

/-- The original scheme and coefficient maps commute on the fixed joint fibers. -/
@[reassoc]
theorem schemeMap_coefficientMap {a b : Under R} (g : a ⟶ b) :
    schemeMap f b ≫ coefficientMap Q g = coefficientMap P g ≫ schemeMap f a := by
  exact congrArg Quiver.Hom.unop
    ((Functor.whiskerRight (rowTransformation f) (functor R)).naturality g)

/-- The native polynomial projection keeps the original scheme restriction square. -/
@[reassoc]
theorem polynomialProjection_schemeMap (a : Under R) :
    schemeMap f ((polynomialUnderFunctor R).obj a) ≫ polynomialProjection Q a =
      polynomialProjection P a ≫ schemeMap f a :=
  schemeMap_coefficientMap f ((polynomialUnderCoefficient R).app a)

/-- The native Laurent projection keeps that same original scheme restriction square. -/
@[reassoc]
theorem laurentProjection_schemeMap (a : Under R) :
    schemeMap f ((laurentUnderFunctor R).obj a) ≫ laurentProjection Q a =
      laurentProjection P a ≫ schemeMap f a :=
  schemeMap_coefficientMap f ((laurentUnderCoefficient R).app a)

/-- The actual polynomial product comparison is natural for scheme-over-base maps. -/
@[reassoc]
theorem polynomialIso_schemeMap (a : Under R) :
    schemeMap f ((polynomialUnderFunctor R).obj a) ≫ (polynomialIso Q a).hom =
      (polynomialIso P a).hom ≫
        (baseProductFunctor (PolynomialLaurent.polynomialProjection integerRing)).map
          (schemeMap f a) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, polynomialIso_hom_fst, baseProductFunctor,
      pullback.lift_fst, polynomialIso_hom_fst_assoc]
    exact polynomialProjection_schemeMap f a
  · simp only [Category.assoc, polynomialIso_hom_snd, baseProductFunctor,
      pullback.lift_snd, Category.comp_id, schemeMap_coefficientProjection_assoc]

/-- The actual Laurent product comparison is natural for the same scheme maps. -/
@[reassoc]
theorem laurentIso_schemeMap (a : Under R) :
    schemeMap f ((laurentUnderFunctor R).obj a) ≫ (laurentIso Q a).hom =
      (laurentIso P a).hom ≫
        (baseProductFunctor (PolynomialLaurent.laurentProjection integerRing)).map
          (schemeMap f a) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, laurentIso_hom_fst, baseProductFunctor,
      pullback.lift_fst, laurentIso_hom_fst_assoc]
    exact laurentProjection_schemeMap f a
  · simp only [Category.assoc, laurentIso_hom_snd, baseProductFunctor,
      pullback.lift_snd, Category.comp_id, schemeMap_coefficientProjection_assoc]

/-- The original positive chart commutes with the original scheme map. -/
@[reassoc]
theorem laurentPlus_schemeMap (a : Under R) :
    schemeMap f ((laurentUnderFunctor R).obj a) ≫ laurentPlus Q a =
      laurentPlus P a ≫ schemeMap f ((polynomialUnderFunctor R).obj a) :=
  schemeMap_coefficientMap f ((underToLaurent R).app a)

/-- The original inverse-coordinate chart retains its distinct scheme restriction square. -/
@[reassoc]
theorem laurentMinus_schemeMap (a : Under R) :
    schemeMap f ((laurentUnderFunctor R).obj a) ≫ laurentMinus Q a =
      laurentMinus P a ≫ schemeMap f ((polynomialUnderFunctor R).obj a) :=
  schemeMap_coefficientMap f ((underToLaurentInvert R).app a)

end AlgebraicGeometry.Scheme.BaseChange.Coefficients
