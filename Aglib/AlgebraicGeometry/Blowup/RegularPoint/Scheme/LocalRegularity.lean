/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Scheme

/-! # Local regularity above a regular point -/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

/-- Regularity over the actual closed centre only needs regularity of its
original local ring of dimension two, not regularity of the whole scheme. -/
theorem regularLocalRing_pointBlowup_over_regularPoint
    (Y : Scheme.{u}) (y : Y) (hy : IsClosed ({y} : Set Y))
    [IsRegularLocalRing (Y.presheaf.stalk y)]
    (hd : ringKrullDim (Y.presheaf.stalk y) = 2)
    (z : (blowupDatum (Y.fromSpecResidueField y).ker).Y)
    (hz : (blowupDatum (Y.fromSpecResidueField y).ker).map z = y) :
    IsRegularLocalRing ((blowupDatum (Y.fromSpecResidueField y).ker).Y.presheaf.stalk z) := by
  let B := blowupDatum (Y.fromSpecResidueField y).ker
  have hlocal : RegularStalks (pullback B.map (Y.fromSpecStalk y)) :=
    (regularStalks (Y.presheaf.stalk y) hd).of_isOpenImmersion (stalkBlowupIso Y y hy).inv
  have hlift : z ∈ Set.range (pullback.fst B.map (Y.fromSpecStalk y)) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨closedPoint (Y.presheaf.stalk y), Scheme.fromSpecStalk_closedPoint.trans hz.symm⟩
  obtain ⟨w, rfl⟩ := hlift
  let : IsRegularLocalRing ((pullback B.map (Y.fromSpecStalk y)).presheaf.stalk w) := hlocal w
  let : IsIso ((pullback.fst B.map (Y.fromSpecStalk y)).stalkMap w) :=
    stalkBlowupProjection_isIso_stalkMap Y y w
  exact IsRegularLocalRing.of_ringEquiv
    (asIso ((pullback.fst B.map (Y.fromSpecStalk y)).stalkMap w)).commRingCatIsoToRingEquiv.symm

end AlgebraicGeometry.Scheme.Blowup.RegularPoint
