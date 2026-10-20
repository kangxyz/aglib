/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Reducedness of actual etale fibres

Source: `lean/R5Lab/Aglib/AlgebraicGeometry/Morphisms/Etale/Reduced.lean`.
Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `0d66f34d3ac82db07aad0e2cfd87493396d2de1bc0eac57560b7142889b5449e`.
Native objects and proved suppliers replace application provenance and redundant premises.
-/

@[expose] public section


noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Etale

/-- The existing universal smooth-field normality theorem supplies reduced etale fibres. -/
theorem geometricallyReduced {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] :
    GeometricallyReduced f := by
  constructor
  intro K _ y Z fst snd h
  have : Etale snd := by
    rw [← h.isoPullback_hom_snd]
    infer_instance
  exact (Scheme.smoothFieldNormality K Z snd inferInstance).isReduced

/-- Etale ascent retains the reduced and locally Noetherian target hypotheses. -/
theorem isReduced {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    [IsReduced Y] [IsLocallyNoetherian Y] : IsReduced X := by
  let : GeometricallyReduced f := geometricallyReduced f
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f

end AlgebraicGeometry.Etale
