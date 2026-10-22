/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence
public import Aglib.AlgebraicGeometry.Blowup.TopologicalDensity

/-!
# Topological density along actual admissible sequences

Every dense open of the original locally Noetherian base remains dense after
the recorded sequence. The open need not be the protected open, and no
schematic-density or reducedness assumption is made.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Blowup.AdmissibleSequence

/-- Actual admissible sequences preserve topological density of every open
on a locally Noetherian base, independently of their protected open. -/
theorem preimage_open_dense {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    {U : X.Opens} {β : Y ⟶ X} (hβ : AdmissibleSequence U β)
    (W : X.Opens) (hW : Dense (W : Set X)) :
    Dense ((β ⁻¹ᵁ W) : Set Y) := by
  induction hβ with
  | id => exact hW
  | @step T δ hδ J B hJ ih =>
      let : IsProper δ := hδ.isProper
      let : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian δ
      exact B.preimage_open_dense (δ ⁻¹ᵁ W) ih
  | iso hδ e ih =>
      exact ih.preimage e.hom.isOpenEmbedding.isOpenMap

end AlgebraicGeometry.Scheme.Blowup.AdmissibleSequence
