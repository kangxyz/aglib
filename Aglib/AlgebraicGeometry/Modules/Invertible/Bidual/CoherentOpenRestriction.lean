/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Locality


/-!
# Coherent inputs supply the original bidual restriction map

All quasicoherence inputs to the actual affine bidual restriction map are
derived from the original finite-type sheaf on the locally Noetherian model.
The open chart is locally Noetherian because its original map is open.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {R : CommRingCat.{u}}
  (j : Spec R ⟶ X) [IsOpenImmersion j] (M : X.Modules)
  (hM : affineLocallyFiniteType X M)

/-- Coherence derives every input to the original affine bidual restriction map. -/
def coherentBidualOpenRestriction :
    (show X.Modules from dualSheaf X (dualSheaf X M)).restrict j ⟶
      dualSheaf (Spec R) (dualSheaf (Spec R) (M.restrict j)) := by
  let : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion j
  let : (M.restrict j).IsQuasicoherent := (hM R j).1
  let : ((show X.Modules from dualSheaf X M).restrict j).IsQuasicoherent :=
    ((affineLocallyFiniteType_dualSheaf M hM) R j).1
  let : ((show X.Modules from dualSheaf X (dualSheaf X M)).restrict j).IsQuasicoherent :=
    ((affineLocallyFiniteType_bidualSheaf M hM) R j).1
  have hlocal := affineLocallyFiniteType_restrict j hM
  let : (dualSheaf (Spec R) (M.restrict j)).IsQuasicoherent :=
    quasicoherent_of_affineLocallyFiniteType
      (affineLocallyFiniteType_dualSheaf (M.restrict j) hlocal)
  let : (dualSheaf (Spec R) (dualSheaf (Spec R) (M.restrict j))).IsQuasicoherent :=
    quasicoherent_of_affineLocallyFiniteType
      (affineLocallyFiniteType_bidualSheaf (M.restrict j) hlocal)
  exact affineBidualOpenRestriction j M

/-- The original evaluation square has no additional quasicoherence premises. -/
theorem coherentBidualOpenRestriction_evaluation :
    (restrictFunctor j).map (bidualMap X M) ≫ coherentBidualOpenRestriction j M hM =
      bidualMap (Spec R) (M.restrict j) := by
  let : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion j
  let : (M.restrict j).IsQuasicoherent := (hM R j).1
  let : ((show X.Modules from dualSheaf X M).restrict j).IsQuasicoherent :=
    ((affineLocallyFiniteType_dualSheaf M hM) R j).1
  let : ((show X.Modules from dualSheaf X (dualSheaf X M)).restrict j).IsQuasicoherent :=
    ((affineLocallyFiniteType_bidualSheaf M hM) R j).1
  have hlocal := affineLocallyFiniteType_restrict j hM
  let : (dualSheaf (Spec R) (M.restrict j)).IsQuasicoherent :=
    quasicoherent_of_affineLocallyFiniteType
      (affineLocallyFiniteType_dualSheaf (M.restrict j) hlocal)
  let : (dualSheaf (Spec R) (dualSheaf (Spec R) (M.restrict j))).IsQuasicoherent :=
    quasicoherent_of_affineLocallyFiniteType
      (affineLocallyFiniteType_bidualSheaf (M.restrict j) hlocal)
  exact affineBidualOpenRestriction_evaluation j M

end AlgebraicGeometry.Scheme.Modules.Invertible
