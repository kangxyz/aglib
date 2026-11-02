/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ResidueFiber
public import Aglib.AlgebraicGeometry.Curves.Projectivity.Graph
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Comparison
public import Aglib.AlgebraicGeometry.Dimension.Finite
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Dimension of the literal closed fibre

An integral algebra contracts strict chains of prime ideals strictly. Applying
this fact on the inverse images of affine opens bounds the dimension of a
finite cover of the projective line, including empty and nonreduced covers.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

/-- Every finite cover of the projective line over a field has dimension at most one. -/
theorem finite_projectiveLine_topologicalKrullDim_le_one
    {K : Type u} [Field K] {Y : Scheme.{u}}
    (p : Y ⟶ ProjectiveLine.projectiveP1 K) [IsFinite p] :
    topologicalKrullDim Y ≤ 1 := by
  have hd : topologicalKrullDim (ProjectiveLine.projectiveP1 K) = 1 := by
    let e := ProjectiveLine.TwoChart.twoChartLineIsoProjectiveP1 K
    exact (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).symm.trans
      (Scheme.OverField.Curve.Projectivity.twoChartLine_topologicalKrullDim K)
  exact (p.topologicalKrullDim_le_of_isFinite).trans hd.le

/-- The actual closed fibre has dimension at most one, without Noetherianity of the base. -/
theorem residueFiber_topologicalKrullDim_le_one
    {R : Type u} [CommRing R] [IsLocalRing R] {Y : Scheme.{u}}
    (p : Y ⟶ ProjectiveLine.projectiveP1 R) [IsFinite p] :
    topologicalKrullDim (residueFiber p) ≤ 1 :=
  finite_projectiveLine_topologicalKrullDim_le_one (residueFiberLineMap p)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
