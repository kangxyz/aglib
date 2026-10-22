/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.Absolute
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.Closed
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.Separated

/-!
# Separated finite-presentation closed envelopes over arbitrary affine bases

A separated finite-type morphism to an arbitrary affine base is a closed
subscheme of a separated finitely presented scheme over that same base.
The proof constructs an arithmetic system, captures finite-type graphs at an
actual stage, and then passes to an actual finitely presented closed
approximant where separatedness holds. No Noetherian hypothesis or supplied
model/existence packet appears in the conclusion or its assumptions.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- Every separated finite-type scheme over an affine base has an actual
separated finite-presentation closed envelope over the original base. -/
@[stacks 01ZJ]
lemma exists_closed_finitePresentation_envelope
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ S) (i : X ⟶ Y),
      IsClosedImmersion i ∧ LocallyOfFinitePresentation g ∧
      QuasiCompact g ∧ IsSeparated g ∧ i ≫ g = f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨M⟩ := FinitePresentationEnvelope.nonempty_system X
  obtain ⟨Y, g, i, hi, hg, hqc, hqs, hcomm⟩ :=
    M.exists_closed_finitePresentation_envelope f
  let : IsClosedImmersion i := hi
  let : LocallyOfFinitePresentation g := hg
  let : QuasiCompact g := hqc
  let : QuasiSeparated g := hqs
  exact exists_separated_finitePresentation_envelope_of_closed f g i hcomm

end AlgebraicGeometry.Scheme
