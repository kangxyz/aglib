/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Reduced
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Geometric reducedness of an actual smooth morphism

Source: `R5Lab.AlgebraicGeometry.EllipticCurve.Tate.Classification`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, original lines 99–108.
Only the stated generic slice is admitted; its actual objects, maps and hypotheses are retained.
-/

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme
universe u

/-- Every actual field base change of a smooth morphism has a reduced source. -/
theorem geometricallyReduced_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] :
    GeometricallyReduced f := by
  constructor
  intro K _ y Z fst snd h
  let : Smooth snd := MorphismProperty.of_isPullback h inferInstance
  exact isReduced_of_smooth_over_field snd

end AlgebraicGeometry.Scheme
