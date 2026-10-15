/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Noetherian
/-!
# Finite-type pullback from a locally Noetherian scheme

The native module-sheaf pullback restricts to the chart-based finite-type
quasicoherent category when the scheme carrying the input sheaf is locally
Noetherian. That hypothesis supplies finite presentation. The receiving
scheme is arbitrary; no flatness or local Noetherianity is assumed there.

The inclusion, identity, composition and open-restriction comparisons
retain the actual geometric module-sheaf maps. Exact coherent pullback
under flatness belongs to the higher coherent family.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]

/-- Pullback preserves the chart-based finite-type quasicoherent predicate
from a locally Noetherian scheme into an arbitrary receiving scheme. -/
theorem affineLocallyFiniteType_pullback (f : X ⟶ Y) {M : Y.Modules} (hM : affineLocallyFiniteType Y
  M) :
    affineLocallyFiniteType X ((Scheme.Modules.pullback f).obj M) := by
  have := affineLocallyFiniteType_finitePresentation hM
  exact affineLocallyFiniteType_of_finitePresentation _

/-- The actual geometric pullback on finite-type quasicoherent sheaves.
Local Noetherianity is required only of the scheme carrying the input. -/
def finiteTypePullback (f : X ⟶ Y) : FiniteTypeSheaves Y ⥤ FiniteTypeSheaves X :=
  (affineLocallyFiniteType X).lift (finiteTypeSheavesToModules Y ⋙ Scheme.Modules.pullback f)
    (fun M => affineLocallyFiniteType_pullback f M.property)

/-- The finite-type sheaf inclusion recovers the original geometric module-sheaf pullback. -/
@[simp] theorem finiteTypePullback_comp_inclusion (f : X ⟶ Y) :
    finiteTypePullback f ⋙ finiteTypeSheavesToModules X =
      finiteTypeSheavesToModules Y ⋙ Scheme.Modules.pullback f := rfl

instance finiteTypePullback_additive (f : X ⟶ Y) : (finiteTypePullback f).Additive := by
  dsimp [finiteTypePullback]
  infer_instance

/-- Identity comparison inherited from actual geometric pullback. -/
def finiteTypePullbackIdIso (X : Scheme.{u}) [IsLocallyNoetherian X] :
    finiteTypePullback (𝟙 X) ≅ 𝟭 (FiniteTypeSheaves X) :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules X)
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules X) (Scheme.Modules.pullbackId X))

/-- Composition comparison inherited from actual geometric pullback. -/
def finiteTypePullbackCompIso {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    finiteTypePullback (f ≫ g) ≅ finiteTypePullback g ⋙ finiteTypePullback f :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules X)
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules Z) (Scheme.Modules.pullbackComp f g).symm)

/-- On open immersions the finite-type pullback agrees with actual restriction. -/
def finiteTypeRestrictionIsoPullback (j : X ⟶ Y) [IsOpenImmersion j] :
    finiteTypeSheavesRestriction j ≅ finiteTypePullback j :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules X)
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules Y)
      (Scheme.Modules.restrictFunctorIsoPullback j))

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
