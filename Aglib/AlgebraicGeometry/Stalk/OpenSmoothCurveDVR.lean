/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.EtaleCurveDVR

/-!
# Closed-point DVR stalks from actual smooth open charts

Source: `R5Lab/Aglib/AlgebraicGeometry/Stalk/OpenSmoothCurveDVR.lean`,
R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`8ad293a032d7906522072a5d0cbb7e2a7b34a0056e004aae2c61089d0569cc6f`.
The arbitrary open chart, original closed image, actual stalk-map isomorphism and
supplied smooth regularity/dimension families are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

open _root_.AlgebraicGeometry.Scheme (SmoothFieldRegularity SmoothClosedPointDimension)

namespace AlgebraicGeometry.Scheme

/-- A closed point in an actual smooth curve chart has a DVR stalk.
The smooth regularity and closed-point dimension families are the existing ones. -/
theorem smoothChart_closedPoint_dvr {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral Y] (j : X ⟶ Y) [IsOpenImmersion j]
    (p : Y ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 (j ≫ p)]
    (hreg : SmoothFieldRegularity.{u}) (hdim : SmoothClosedPointDimension.{u})
    (q : X) (hq : IsClosed ({j q} : Set Y)) :
    IsDiscreteValuationRing (Y.presheaf.stalk (j q)) := by
  let : Nonempty X := ⟨q⟩
  let : IsIntegral X := isIntegral_of_isOpenImmersion j
  have hc : IsClosed ({q} : Set X) := by
    convert hq.preimage j.continuous using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, j.isOpenEmbedding.injective.eq_iff]
  have hr := hreg k X (j ≫ p) (SmoothOfRelativeDimension.smooth 1 (j ≫ p)) q
  let := hr
  have hd := hdim k X (j ≫ p) 1 inferInstance q hc
  have : IsDiscreteValuationRing (X.presheaf.stalk q) := by
    apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
    have he := (IsRegularLocalRing.iff_finrank_cotangentSpace (X.presheaf.stalk q)).mp hr
    rw [hd] at he
    exact_mod_cast he
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (asIso (j.stalkMap q)).commRingCatIsoToRingEquiv.symm

end AlgebraicGeometry.Scheme
