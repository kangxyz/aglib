/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.FiniteModel
public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.EulerCharacteristic

/-!
# Locally constant original proper fibre Euler characteristics

The proper supplier constructs the same actual bounded finite-projective
model. Its original ordinary fibre comparison identifies the unchanged
intrinsic alternating sum with the native homological Euler characteristic.
Finite-projective terms make it locally constant without reducedness.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The intrinsic alternating sum of original proper ordinary fibre-cohomology dimensions
is locally constant for a coherent relatively flat coefficient over a Noetherian affine base. -/
theorem isLocallyConstant_moduleFiberEulerChar_of_proper
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) :
    IsLocallyConstant (moduleFiberEulerChar f M) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  obtain ⟨n, U, hU, hcover, ⟨D⟩⟩ :=
    exists_finiteCechCohomologyModel_of_proper (.of R) f M hM hflat
  exact D.isLocallyConstant_moduleFiberEulerChar hU hcover Equiv.ulift hflat

end AlgebraicGeometry.Scheme.Cohomology
