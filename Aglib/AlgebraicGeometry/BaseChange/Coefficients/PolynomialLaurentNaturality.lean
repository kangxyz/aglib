/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.PolynomialLaurent

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/CoefficientPolynomialLaurentNaturality.lean` at LOCAL
Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 124]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Naturality of actual native coefficient polynomial and Laurent products

The actual pullback isomorphisms are natural for every coefficient arrow. No
compactness, flatness or quasi-separatedness hypothesis enters this geometric leaf.

This module supplies the original ambient coefficient maps and chart transport.
It does not claim supported-group comparisons, assembled scheme-restriction
naturality, seed invertibility, stabilization, telescope or TT identification.
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
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The original native polynomial projection square for every coefficient arrow. -/
@[reassoc] theorem polynomialProjection_naturality {a b : Under R} (g : a ⟶ b) :
    coefficientMap P ((polynomialUnderFunctor R).map g) ≫ polynomialProjection P a =
      polynomialProjection P b ≫ coefficientMap P g := by
  change coefficientMap P ((polynomialUnderFunctor R).map g) ≫
    coefficientMap P ((polynomialUnderCoefficient R).app a) =
      coefficientMap P ((polynomialUnderCoefficient R).app b) ≫ coefficientMap P g
  rw [← coefficientMap_comp, ← coefficientMap_comp]
  exact congrArg (coefficientMap P) ((polynomialUnderCoefficient R).naturality g).symm

/-- The original native Laurent projection square for every coefficient arrow. -/
@[reassoc] theorem laurentProjection_naturality {a b : Under R} (g : a ⟶ b) :
    coefficientMap P ((laurentUnderFunctor R).map g) ≫ laurentProjection P a =
      laurentProjection P b ≫ coefficientMap P g := by
  change coefficientMap P ((laurentUnderFunctor R).map g) ≫
    coefficientMap P ((laurentUnderCoefficient R).app a) =
      coefficientMap P ((laurentUnderCoefficient R).app b) ≫ coefficientMap P g
  rw [← coefficientMap_comp, ← coefficientMap_comp]
  exact congrArg (coefficientMap P) ((laurentUnderCoefficient R).naturality g).symm

/-- Actual polynomial pullback comparisons are natural for every original coefficient map. -/
@[reassoc] theorem polynomialIso_naturality {a b : Under R} (g : a ⟶ b) :
    coefficientMap P ((polynomialUnderFunctor R).map g) ≫ (polynomialIso P a).hom =
      (polynomialIso P b).hom ≫
        (baseProductFunctor (PolynomialLaurent.polynomialProjection integerRing)).map
          (coefficientMap P g) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, polynomialIso_hom_fst, baseProductFunctor,
      pullback.lift_fst, polynomialIso_hom_fst_assoc]
    exact polynomialProjection_naturality P g
  · simp only [Category.assoc, polynomialIso_hom_snd, baseProductFunctor,
      pullback.lift_snd, Category.comp_id]
    rw [coefficientMap_coefficientProjection_assoc]
    change coefficientProjection (op P, (polynomialUnderFunctor R).obj b) ≫
      Spec.map (polynomialMap g.right) ≫ Spec.map (polynomialMap (integerMap a.right)) = _
    rw [← Spec.map_comp, ← polynomialMap_comp, integerMap_naturality]

/-- Actual Laurent pullback comparisons are natural for every original coefficient map. -/
@[reassoc] theorem laurentIso_naturality {a b : Under R} (g : a ⟶ b) :
    coefficientMap P ((laurentUnderFunctor R).map g) ≫ (laurentIso P a).hom =
      (laurentIso P b).hom ≫
        (baseProductFunctor (PolynomialLaurent.laurentProjection integerRing)).map
          (coefficientMap P g) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, laurentIso_hom_fst, baseProductFunctor,
      pullback.lift_fst, laurentIso_hom_fst_assoc]
    exact laurentProjection_naturality P g
  · simp only [Category.assoc, laurentIso_hom_snd, baseProductFunctor,
      pullback.lift_snd, Category.comp_id]
    rw [coefficientMap_coefficientProjection_assoc]
    change coefficientProjection (op P, (laurentUnderFunctor R).obj b) ≫
      Spec.map (laurentMap g.right) ≫ Spec.map (laurentMap (integerMap a.right)) = _
    rw [← Spec.map_comp, ← laurentMap_comp, integerMap_naturality]

/-- The genuine opposite polynomial identification uses the original geometric inverse. -/
def polynomialRowIso :
    polynomialUnderFunctor R ⋙ row P ⋙ functor R ≅
      (row P ⋙ functor R) ⋙
        (baseProductFunctor (PolynomialLaurent.polynomialProjection integerRing)).op :=
  NatIso.ofComponents (fun a ↦ (polynomialIso P a).symm.op) (by
    intro a b g
    apply Quiver.Hom.unop_inj
    change (polynomialIso P b).inv ≫
      coefficientMap P ((polynomialUnderFunctor R).map g) =
        (baseProductFunctor (PolynomialLaurent.polynomialProjection integerRing)).map
          (coefficientMap P g) ≫ (polynomialIso P a).inv
    apply (cancel_mono (polynomialIso P a).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [polynomialIso_naturality P g, Iso.inv_hom_id_assoc])

/-- The genuine opposite Laurent identification keeps the same original inverse variance. -/
def laurentRowIso :
    laurentUnderFunctor R ⋙ row P ⋙ functor R ≅
      (row P ⋙ functor R) ⋙
        (baseProductFunctor (PolynomialLaurent.laurentProjection integerRing)).op :=
  NatIso.ofComponents (fun a ↦ (laurentIso P a).symm.op) (by
    intro a b g
    apply Quiver.Hom.unop_inj
    change (laurentIso P b).inv ≫
      coefficientMap P ((laurentUnderFunctor R).map g) =
        (baseProductFunctor (PolynomialLaurent.laurentProjection integerRing)).map
          (coefficientMap P g) ≫ (laurentIso P a).inv
    apply (cancel_mono (laurentIso P a).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [laurentIso_naturality P g, Iso.inv_hom_id_assoc])

/-- Forward opposite polynomial components retain precisely the geometric inverse. -/
@[simp] theorem polynomialRowIso_hom_app (a : Under R) :
    (polynomialRowIso P).hom.app a = (polynomialIso P a).inv.op := rfl

/-- Forward opposite Laurent components retain precisely the geometric inverse. -/
@[simp] theorem laurentRowIso_hom_app (a : Under R) :
    (laurentRowIso P).hom.app a = (laurentIso P a).inv.op := rfl

end AlgebraicGeometry.Scheme.BaseChange.Coefficients
