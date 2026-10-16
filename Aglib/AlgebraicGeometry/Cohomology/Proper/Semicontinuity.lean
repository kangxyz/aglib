/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.FiniteModel
public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.Semicontinuity

/-!
# Upper semicontinuity of original proper fibre cohomology

Proper finiteness and relative flatness internally construct the same
finite-cover model. Its original ordinary fibre comparison transports native
finite-complex semicontinuity to the unchanged fibre-cohomology dimension.
No projective embedding, model family or reducedness assumption is input.
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

/-- Original ordinary fibre-cohomology dimension is upper semicontinuous for a coherent
relatively flat coefficient under a proper morphism over a Noetherian affine base. -/
theorem upperSemicontinuous_moduleFiberCohomologyDimension_of_proper
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ) :
    UpperSemicontinuous (moduleFiberCohomologyDimension f M q) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  obtain ⟨n, U, hU, hcover, ⟨D⟩⟩ :=
    exists_finiteCechCohomologyModel_of_proper (.of R) f M hM hflat
  exact D.upperSemicontinuous_fiberCohomologyDimension hU hcover Equiv.ulift hflat q

end AlgebraicGeometry.Scheme.Cohomology
