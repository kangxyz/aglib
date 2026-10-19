/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.GeometricRegularity.Field
public import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Smoothness and geometrically regular fibers

A locally finitely presented morphism is smooth exactly when it is flat and all
its geometric fibers have regular local rings. Over a locally Noetherian base,
local finite type supplies the finite-presentation hypothesis.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Flatness and geometric regularity of the fibers imply smoothness for a locally
finitely presented morphism over any base. -/
theorem Smooth.of_flat_of_geometricallyRegular [LocallyOfFinitePresentation f]
    [Flat f] [GeometricallyRegular f] : Smooth f := by
  apply Smooth.of_smooth_fiberToSpecResidueField
  intro y
  let : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd f (Y.fromSpecResidueField y)))
  exact Smooth.of_geometricallyRegular_of_field (f.fiberToSpecResidueField y)

/-- The geometric-fiber criterion for a locally finitely presented morphism. -/
theorem smooth_iff_flat_and_geometricallyRegular [LocallyOfFinitePresentation f] :
    Smooth f ↔ Flat f ∧ GeometricallyRegular f := by
  constructor
  · intro hf
    let := hf
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hflat, hregular⟩
    let := hflat
    let := hregular
    exact Smooth.of_flat_of_geometricallyRegular f

/-- Over a locally Noetherian base, smoothness is local finite type together with
flatness and geometric regularity of all fibers. -/
theorem smooth_iff_locallyOfFiniteType_and_flat_and_geometricallyRegular
    [IsLocallyNoetherian Y] :
    Smooth f ↔ LocallyOfFiniteType f ∧ Flat f ∧ GeometricallyRegular f := by
  constructor
  · intro hf
    let := hf
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · rintro ⟨hfinite, hflat, hregular⟩
    let := hfinite
    let := hflat
    let := hregular
    exact Smooth.of_flat_of_geometricallyRegular f

end AlgebraicGeometry
