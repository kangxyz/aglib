/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.CoefficientOpenZeroTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence

/-! # Returning a composite zero through an original coefficient comparison

The actual pullback class is transported through a specified coefficient
isomorphism. Original coefficient naturality and pullback composition give
zero after its next restriction. A detector for that actual coefficient
therefore returns zero of the original first restriction. No comparison
equation or replacement-class zero is an additional premise.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u eY eU eV

attribute [local instance] hasSheafifyLarge

/-- Composite zero descends through a coefficient isomorphism and a genuine
zero detector for the next restriction. The three Ext worlds are independent. -/
theorem restriction_zero_of_composite_zero_of_iso_detector
    {Y U V : Scheme.{u}}
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eU} (AbelianSheaf.{u, u + 1} U)]
    [HasExt.{eV} (AbelianSheaf.{u, u + 1} V)]
    (u : U ⟶ Y) (k : V ⟶ U)
    (F : AbelianSheaf.{u, u + 1} Y) (G : AbelianSheaf.{u, u + 1} U)
    (e : (inverseImage u).obj F ≅ G) (q : ℕ) (c : Sheaf.H.{eY} F q)
    (hdetect : ∀ d : Sheaf.H.{eU} G q,
      cohomologyPullback.{u, eU, eV} (X := U) (S := V) k G q d = 0 → d = 0)
    (hc : cohomologyPullback.{u, eY, eV} (X := Y) (S := V) (k ≫ u) F q c = 0) :
    cohomologyPullback.{u, eY, eU} (X := Y) (S := U) u F q c = 0 := by
  have hz : Sheaf.H.map e.hom q
      (cohomologyPullback.{u, eY, eU} u F q c) = 0 :=
    hdetect _ (coefficient_restriction_zero_of_composite_zero u k F G e.hom q c hc)
  exact (cohomologyMapIso_bijective e q).injective
    (hz.trans (map_zero _).symm)

end AlgebraicGeometry.Scheme.EtaleCohomology
