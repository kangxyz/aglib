/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Core
public import Aglib.AlgebraicGeometry.Curves.SmoothGeometry
public import Aglib.AlgebraicGeometry.Stalk.CodimensionOne
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# Actual closed DVR stalks over the original field

Native smooth-field stalk normality and the existing ordinary closed-point
dimension family yield every actual closed DVR stalk on the same curve over F.
No algebraically closed base, regularity family, arbitrary local ring, or
geometric-fibre replacement is used. The closed-point dimension foundation
remains explicit. Source scope: horizontal extension in K2-018 at manuscript
e73d98b1b5c1e5abcdebf7d058e436d792b87982.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothClosedPointDimension)
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)


@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve.ClosedStalks
universe u

/-- The actual closed-point stalk is a DVR over the ORIGINAL field F.
Regularity is not supplied: normality is native, and codimension-one DVR
realization is the existing actual local-ring theorem. -/
theorem closedPoint_stalk_dvr (F : Type u) [Field F]
    (hclosed : SmoothClosedPointDimension.{u}) (Y : FScheme F) (hY : Properties Y)
    (x : Y.left) (hx : IsClosed ({x} : Set Y.left)) :
    letI : IsIntegral Y.left := hY.isIntegral
    IsDiscreteValuationRing (Y.left.presheaf.stalk x) := by
  let : IsIntegral Y.left := hY.isIntegral
  let : IsNoetherian Y.left := curveProperties_isNoetherian hY
  let : SmoothOfRelativeDimension 1 Y.hom := hY.smooth
  let : ∀ y : Y.left, IsIntegrallyClosed (Y.left.presheaf.stalk y) :=
    fun y => (Scheme.smoothFieldNormality F Y.left Y.hom
      (SmoothOfRelativeDimension.smooth 1 Y.hom) y).2
  let z : CodimensionOnePoint Y.left :=
    ⟨x, curveProperties_closedPoint_stalk_dimension hclosed hY x hx⟩
  exact CodimensionOnePoint.localRing_isDiscreteValuationRing z

end AlgebraicGeometry.Scheme.OverField.Curve.ClosedStalks
