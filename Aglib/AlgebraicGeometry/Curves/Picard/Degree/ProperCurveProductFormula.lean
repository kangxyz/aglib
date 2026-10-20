/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.Field
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree.CommonQuotientDegree
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# The original proper-curve product formula from proved curve H1 finiteness

Native proper structure-sheaf cohomology finiteness at degree one supplies
the original proper-curve common-quotient/Euler endpoint. The producer has exactly
`ProperCurveProductFormula.{u}` as its type, with no additional theorem-family
parameter. Singular curves, arbitrary fields, residue weights and the original
order definition are retained.
-/

open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)



@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree
universe u

/-- The literal original product-formula family, using proved actual curve H1 finiteness. -/
theorem properCurveProductFormula : ProperCurveProductFormula.{u} := by
  intro K hK X hIntegral hNoetherian p hProper hdim
  let Y : FScheme K := Over.mk p
  let : IsIntegral Y.left := hIntegral
  let : AlgebraicGeometry.IsNoetherian Y.left := hNoetherian
  let : IsProper Y.hom := hProper
  exact CommonQuotientDegree.principalProductFormula_of_structureH1_finite Y hdim
    (Scheme.Cohomology.properStructureCohomologyFinite
      K Y 1 hProper)

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.Degree
