/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.IdealFrames

public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Charts
public import Aglib.AlgebraicGeometry.Blowup.UnitLocus
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorOpenLocus


/-!
# The original raw blowdown arrow on the actual unit locus

Use the native unit-chart map into the original blowup and its original
triangle to the base principal open. The original raw pullback arrow is
therefore invertible there, not merely generically presumed invertible.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Blowup.RegularPoint AlgebraicGeometry.Scheme.Blowup.IdealFrames

universe u


open AlgebraicGeometry.Scheme.Modules.Differentials

namespace AlgebraicGeometry.Scheme.Blowup

/-- The actual raw blowdown arrow becomes an isomorphism on each original unit chart. -/
theorem ideal_rawPullback_unitChart_isIso (Λ R : Type u)
    [CommRing Λ] [CommRing R] [Algebra Λ R] (I : Ideal R) (a : I) (n : ℕ) :
    let B := Blowup.blowupDatum (Blowup.affineCenter R I)
    let H := Blowup.affineAtlas B
    IsIso ((pullback (Blowup.UnitLocus.unitChartMap H a)).map
      (rawFormsPullback (Spec.map (CommRingCat.ofHom (algebraMap Λ R))) (blowdown I) n)) := by
  intro B H
  let _ : IsOpenImmersion (Blowup.UnitLocus.unitChartMap H a ≫ blowdown I) := by
    rw [Blowup.UnitLocus.unitChartMap_triangle H a]
    infer_instance
  exact rawFormsPullback_isIso_on_openLocus
    (Spec.map (CommRingCat.ofHom (algebraMap Λ R))) (blowdown I)
    (Blowup.UnitLocus.unitChartMap H a) n

end AlgebraicGeometry.Scheme.Blowup
