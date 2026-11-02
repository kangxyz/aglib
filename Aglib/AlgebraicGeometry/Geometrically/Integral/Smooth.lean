/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Properties.Normal.Components
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Geometric integrality of smooth morphisms with connected fibres

The original smooth-field normality theorem and actual normal-component
argument apply in arbitrary dimension. The geometric statement uses each
original field-valued base change, without selecting another fibre model.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- A connected smooth scheme over any field is integral in arbitrary dimension. -/
theorem isIntegral_of_connected_of_smooth
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] [ConnectedSpace X] : IsIntegral X := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact isIntegral_of_connected_normalStalks_actual X
    (smoothFieldNormality K X f inferInstance)

/-- Smooth morphisms with geometrically connected fibres have geometrically
integral fibres, with no relative-dimension or properness assumption. -/
theorem geometricallyIntegral_of_smooth_of_geometricallyConnected
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [GeometricallyConnected f] :
    GeometricallyIntegral f := by
  constructor
  intro K _ s Z fst snd h
  let : Smooth snd := MorphismProperty.of_isPullback h (inferInstance : Smooth f)
  let : ConnectedSpace Z := GeometricallyConnected.geometrically_connectedSpace s fst snd h
  exact isIntegral_of_connected_of_smooth snd

end AlgebraicGeometry.Scheme
