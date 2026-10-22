/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.Proper
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.FiniteType

/-!
# Proper finite-presentation approximation over an arbitrary affine base

Every proper scheme over an affine base is the original limit of an actual
small cofiltered system of proper finitely presented schemes over that same
base. The transitions and projections are closed immersions. Both the ambient
finite-presentation envelope and its closed-subscheme approximation are
constructed; no approximation supplier is an additional hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Approximation

/-- A proper morphism to an arbitrary affine base admits an actual proper
finite-presentation approximation over that unchanged base, with the original
scheme as limit and closed transition maps and projections. -/
@[stacks 09ZR]
theorem nonempty_properFinitePresentationSystem
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [IsProper f] :
    Nonempty (ProperFinitePresentationSystem f) := by
  obtain ⟨Y, g, i, hi, hfp, hqc, hsep, hcomm⟩ :=
    Scheme.exists_closed_finitePresentation_envelope f
  let : IsClosedImmersion i := hi
  let : LocallyOfFinitePresentation g := hfp
  let : QuasiCompact g := hqc
  let : IsSeparated g := hsep
  let YS : Over S := Over.mk g
  have : LocallyOfFinitePresentation YS.hom := hfp
  have : QuasiCompact YS.hom := hqc
  have : IsSeparated YS.hom := hsep
  exact nonempty_properSystem_of_closed_finitePresentation_envelope f YS i hcomm

end AlgebraicGeometry.Scheme.Approximation
