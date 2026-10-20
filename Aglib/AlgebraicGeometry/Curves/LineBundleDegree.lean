/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Core
public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorInverse
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# The actual Picard-degree homomorphism on field curves

This adapter discharges integrality, Noetherianity, closed DVR stalks and
absolute dimension from Properties, then applies C's actual residue-weighted
Picard degree transported through its proved O(D) equivalence. It introduces
no degree function or new standard theorem family. The only parameters are
the previously disclosed B1 geometric families and C's proper product formula.
There is no coherent-genus, differential, or Riemann–Hurwitz dependency.

Incoming Picard.DivisorInverse SHA256
e5d590b08653fa393d5657a7bf3dece2482b543867c27b33db2b6a6e70187a27.
Application K2-018#prop:k2018-arithmetic-characters, mathematical source
e73d98b1b5c1e5abcdebf7d058e436d792b87982; engineering basis
7f86e4a1763cc4ec35e9b0a8acd659750355a0de and unchanged pins.
-/

open _root_.AlgebraicGeometry.Scheme
  (NormalComponentsOpen SmoothClosedPointDimension SmoothFieldDimension SmoothFieldNormality
    SmoothFieldRegularity)
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u
open Divisors
variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable {F : Type u} [Field F] (X : FScheme F) (hX : Properties X)

def curveDegree : Invertible.PicardGroup X.left →+ ℤ := by
  letI := curveProperties_isIntegral hnormal hcomp hX
  letI := curveProperties_isNoetherian hX
  letI (x : ClosedPoint X.left) : IsDiscreteValuationRing (X.left.presheaf.stalk x.val) :=
    curveProperties_closedPoint_stalk_dvr hnormal hreg hclosed hX x.val x.property
  letI := hX.proper
  exact Picard.Degree.picardDegree X.left X.hom (le_of_eq (curveProperties_dimension hdim hX))
    (hprod F X.left X.hom (curveProperties_dimension hdim hX))

end AlgebraicGeometry.Scheme.OverField.Curve
