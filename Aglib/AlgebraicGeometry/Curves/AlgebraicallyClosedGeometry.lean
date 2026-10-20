/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.SmoothGeometry
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# Geometry of curves over algebraically closed fields

General curve geometry auxiliaries for the actual geometric-fibre consumer of
K2-018, `lem:k2018-geometric-exact-order`, mathematical source
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Closed points give rational points and discrete valuation stalks; the exact
geometric pullback inherits the curve properties and has dimension at most one.
This module retains the general curve hypotheses of the reviewed source proofs.
-/

open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)


@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve.AlgebraicallyClosedGeometry

section Geometry
universe u

/-- On an algebraically closed base every actual closed point is rational;
therefore the current rational-point DVR theorem supplies every closed stalk. -/
theorem closedPoint_stalk_dvr {C : Type u} [Field C] [IsAlgClosed C]
    (Y : FScheme C) (hY : Properties Y) (x : Y.left) (hx : IsClosed {x}) :
    letI := hY.isIntegral
    IsDiscreteValuationRing (Y.left.presheaf.stalk x) := by
  letI := hY.isIntegral
  letI := hY.smooth
  letI : Smooth Y.hom := SmoothOfRelativeDimension.smooth 1 Y.hom
  let q : RationalPoint C Y.left :=
    ⟨Y.hom, pointOfClosedPoint Y.hom x hx,
      pointOfClosedPoint_comp Y.hom x hx⟩
  have hd := hY.rationalOrigin_isDiscreteValuationRing q rfl
  have hp : q.point = x := pointOfClosedPoint_apply Y.hom x hx _
  letI : IsDiscreteValuationRing q.localRing := hd
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (Y.left.presheaf.stalkCongr (.of_eq hp)).commRingCatIsoToRingEquiv

variable {F : Type u} [Field F] (X : FScheme F) (hX : Properties X)

/-- The exact geometric pullback scheme used by the incoming C constructor. -/
def geometricCurve : FScheme (AlgebraicClosure F) :=
  Over.mk (pullback.snd X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)))))

include hX

theorem geometricCurve_properties : Properties (geometricCurve X) := by
  letI := hX.smooth
  letI := hX.proper
  letI := hX.connected
  refine ⟨?_, ?_, ?_⟩
  · exact MorphismProperty.pullback_snd X.hom _ hX.smooth
  · change IsProper (pullback.snd X.hom _)
    infer_instance
  · change GeometricallyConnected (pullback.snd X.hom _)
    infer_instance

theorem geometricCurve_isIntegral : IsIntegral (geometricCurve X).left :=
  (geometricCurve_properties X hX).isIntegral

theorem geometricCurve_isNoetherian : IsNoetherian (geometricCurve X).left := by
  let hbar := geometricCurve_properties X hX
  letI := hbar.proper
  letI := hbar.smooth
  letI : Smooth (geometricCurve X).hom := SmoothOfRelativeDimension.smooth 1 _
  letI : IsLocallyNoetherian (geometricCurve X).left :=
    LocallyOfFiniteType.isLocallyNoetherian (geometricCurve X).hom
  letI : CompactSpace (geometricCurve X).left :=
    QuasiCompact.compactSpace_of_compactSpace (geometricCurve X).hom
  exact ⟨⟩

theorem geometricCurve_geometricallyIntegral : GeometricallyIntegral (geometricCurve X).hom :=
  (geometricCurve_properties X hX).isGeometricallyIntegral

theorem geometricCurve_closedPoint_stalk_dvr
    (x : (geometricCurve X).left) (hx : IsClosed {x}) :
    letI := geometricCurve_isIntegral X hX
    IsDiscreteValuationRing ((geometricCurve X).left.presheaf.stalk x) :=
  closedPoint_stalk_dvr (geometricCurve X) (geometricCurve_properties X hX) x hx
end Geometry

section Dimension
universe u

/-- Closed-point DVRs bound every point's coheight by specialization to a
closed point; the sober-space order isomorphism then bounds global dimension. -/
theorem curve_dimension_le_one {C : Type u} [Field C] [IsAlgClosed C]
    (Y : FScheme C) (hY : Properties Y) : topologicalKrullDim Y.left ≤ 1 := by
  letI := hY.isIntegral
  letI := hY.smooth
  letI : Smooth Y.hom := SmoothOfRelativeDimension.smooth 1 Y.hom
  letI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  change Order.krullDim (IrreducibleCloseds Y.left) ≤ 1
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y.left)),
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x => ?_
  obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints
    (Z := closure ({x} : Set Y.left))
    (Set.Nonempty.closure (Set.singleton_nonempty x)) isClosed_closure.isLocallyClosed
  have hyx : y ≤ x := specializes_iff_mem_closure.mpr hy
  letI : IsDiscreteValuationRing (Y.left.presheaf.stalk y) :=
    closedPoint_stalk_dvr Y hY y hyclosed
  have hyheight : (Order.coheight y : WithBot ℕ∞) = 1 := by
    rw [← ringKrullDim_stalk_eq_coheight]
    exact IsDiscreteValuationRing.ringKrullDim_eq_one _
  exact (WithBot.coe_le_coe.mpr (Order.coheight_anti hyx)).trans hyheight.le

theorem geometricCurve_dimension_le_one {F : Type u} [Field F]
    (X : FScheme F) (hX : Properties X) :
    topologicalKrullDim (geometricCurve X).left ≤ 1 :=
  curve_dimension_le_one (geometricCurve X) (geometricCurve_properties X hX)
end Dimension

end AlgebraicGeometry.Scheme.OverField.Curve.AlgebraicallyClosedGeometry
