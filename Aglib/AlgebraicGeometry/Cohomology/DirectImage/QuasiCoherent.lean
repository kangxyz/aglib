/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits

/-!
# Quasicoherence of actual higher direct images

Native higher direct images of quasicoherent module sheaves under qcqs
morphisms are quasicoherent on an arbitrary target scheme. The original
higher-image open-restriction comparison reduces every actual affine
chart to the proved affine computation. No injective resolution term is
assumed quasicoherent, and no Noetherianity or finiteness is required.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

/-- Every actual higher direct image of a quasicoherent module under a qcqs morphism is
quasicoherent on the arbitrary target scheme. -/
theorem moduleHigherDirectImage_isQuasicoherent {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived n).obj M).IsQuasicoherent := by
  apply Scheme.Modules.QuasiCoherent.quasicoherent_of_affineCharts
  intro R j _
  let a := pullback.fst f j
  let b := pullback.snd f j
  let h := IsPullback.of_hasPullback f j
  have hq : (((Scheme.Modules.pushforward b).rightDerived n).obj
      (M.restrict a)).IsQuasicoherent :=
    moduleHigherDirectImageAffine_isQuasicoherent b (M.restrict a) n
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((Scheme.Modules.higherDirectImageOpenRestrictionIso a b f j h n).app M).symm hq

end AlgebraicGeometry.Scheme.Cohomology
