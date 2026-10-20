/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.AlgebraicGeometry.Geometrically.Connected.PointedCurve
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! The actual connected finite étale covering source inherits the pointed
geometric-connectedness producer through its original Over-field structure map.
The target's geometric connectedness is not a premise. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField

universe u

example {K : Type u} [Field K] {X Y : FScheme K} (f : X ⟶ Y)
    [SmoothOfRelativeDimension 1 Y.hom] [IsProper Y.hom]
    [IsFinite f.left] [Etale f.left] [ConnectedSpace X.left]
    (o : Spec (.of K) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) :
    GeometricallyConnected X.hom := by
  let : SmoothOfRelativeDimension 1 X.hom := by
    have h := smoothOfRelativeDimension_comp 0 1 f.left Y.hom
    simpa only [Over.w f, Nat.zero_add] using h
  let : IsProper X.hom := by rw [← Over.w f]; infer_instance
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsNoetherian X.left :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace X.hom }
  exact Scheme.geometricallyConnected_of_pointed_proper_smooth_curve X.hom o ho

example {K : Type u} [Field K] (X : FScheme K)
    [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] [IsIntegral X.left]
    (origin : Over.mk (𝟙 (Spec (.of K))) ⟶ X) :
    GeometricallyConnected X.hom := by
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : IsNoetherian X.left :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace X.hom }
  exact Scheme.geometricallyConnected_of_pointed_proper_smooth_curve
    X.hom origin.left (Over.w origin)
