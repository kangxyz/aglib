/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FiniteType.RelativeOverlap

/-!
# Separatedness from actual relative overlap charts

The native left-right product cover is a cover of the actual diagonal
target. Its pullbacks of the diagonal are compared by explicit cartesian
squares with the overlap arrows. Closedness on those charts therefore
implies separatedness.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u v

namespace AlgebraicGeometry.Scheme.RelativeOverlap

/-- Closed overlap arrows on a source-open cover imply that the structural
morphism is separated. No affine or finiteness hypotheses are needed. -/
lemma isSeparated_of_overlap_cover {X S : Scheme.{u}} (f : X ⟶ S)
    {κ : Type v} (U : κ → X.Opens) (hU : iSup U = ⊤)
    (hclosed : ∀ a b, IsClosedImmersion (toProduct f (U a) (U b))) : IsSeparated f := by
  let 𝒰 := X.openCoverOfIsOpenCover U hU
  let productCover := Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 f f
  apply (AlgebraicGeometry.isSeparated_iff f).mpr
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) productCover).mpr
  intro ab
  have : IsClosedImmersion (toProduct f (U ab.1) (U ab.2)) := hclosed ab.1 ab.2
  change IsClosedImmersion
    (pullback.snd (pullback.diagonal f) (productToDiagonalTarget f (U ab.1) (U ab.2)))
  rw [← (isPullback_toProduct f (U ab.1) (U ab.2)).isoPullback_inv_snd]
  infer_instance

end AlgebraicGeometry.Scheme.RelativeOverlap
