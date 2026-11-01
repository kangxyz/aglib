/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.LocalizationColimit
public import Aglib.RingTheory.Henselian.StrictHenselization.LocalStages

/-! # Genuine principal neighborhoods of the original pointed stage

Every stage of the original point-localization diagram is genuinely etale over
the original base. Its point is the original localized point composed with the
actual cone projection. No second presentation-equivalent ring is selected.
-/

@[expose] public noncomputable section

open IsLocalization.PrincipalDiagram

namespace GeometricEtaleNeighborhood

universe u

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
  (X : GeometricEtaleNeighborhood R Ω)

local notation "M" => Ideal.primeCompl (Localization.ResiduePoint.ideal X.point.toRingHom)
local notation "S" => GeometricEtaleColimit.stageLocalRing R Ω X

/-- The actual point of each principal stage in the original localization diagram. -/
def principalStagePoint (s : Finset M) : stage M s →+* Ω :=
  (Localization.ResiduePoint.point X.point.toRingHom).comp (projection M S s)

@[simp] theorem principalStagePoint_algebraMap (s : Finset M) (b : X.algebra) :
    principalStagePoint R Ω X s (algebraMap X.algebra (stage M s) b) = X.point b := by
  change Localization.ResiduePoint.point X.point.toRingHom
    (projection M S s (algebraMap X.algebra (stage M s) b)) = X.point b
  rw [projection_algebraMap]
  exact Localization.ResiduePoint.point_algebraMap X.point.toRingHom b

/-- The whole original point triangle on the genuine affine coefficient stage. -/
theorem principalStagePoint_comp (s : Finset M) :
    (principalStagePoint R Ω X s).comp (algebraMap X.algebra (stage M s)) =
      X.point.toRingHom := by
  ext b
  exact principalStagePoint_algebraMap R Ω X s b

/-- Every literal principal stage remains genuinely etale over the original base. -/
theorem principalStage_etale (s : Finset M) : Algebra.Etale R (stage M s) :=
  Algebra.Etale.comp R X.algebra (stage M s)

/-- The genuine-stage point preserves the original base algebra map. -/
theorem principalStagePoint_base (s : Finset M) :
    (principalStagePoint R Ω X s).comp (algebraMap R (stage M s)) = algebraMap R Ω := by
  ext r
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R X.algebra (stage M s),
    principalStagePoint_algebraMap]
  exact X.point.commutes r

end GeometricEtaleNeighborhood
