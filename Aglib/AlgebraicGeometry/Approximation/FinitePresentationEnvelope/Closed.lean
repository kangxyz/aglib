/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.Graph
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.System

/-!
# Closed finite-presentation envelopes from actual arithmetic systems

A genuine arithmetic approximation system supplies an actual closed envelope
of every finite-type map from its original source to an arbitrary affine base.
The envelope is a literal fiber product of one arithmetic stage and the
original base. Its structural triangle is the native pullback triangle.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope.System

/-- An actual arithmetic system gives an actual closed finitely presented
quasi-separated envelope over the original affine base. -/
lemma exists_closed_finitePresentation_envelope
    {X S : Scheme.{u}} (M : System X) [IsAffine S]
    (f : X ⟶ S) [LocallyOfFiniteType f] :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ S) (i : X ⟶ Y),
      IsClosedImmersion i ∧ LocallyOfFinitePresentation g ∧
      QuasiCompact g ∧ QuasiSeparated g ∧ i ≫ g = f := by
  let s := specULiftZIsTerminal.from S
  let t (i : M.Index) := specULiftZIsTerminal.from (M.diagram.obj i)
  obtain ⟨j, hj⟩ := Scheme.exists_isClosedImmersion_graph_of_isLimit M.diagram M.cone
    M.isLimit specULiftZIsTerminal s t f
  let g := pullback.snd (t j) s
  let i : X ⟶ pullback (t j) s :=
    pullback.lift (M.projection.app j) f (specULiftZIsTerminal.hom_ext _ _)
  have : LocallyOfFinitePresentation (t j) := M.stage_locallyOfFinitePresentation j
  have : QuasiCompact (t j) := inferInstance
  have : QuasiSeparated (t j) := inferInstance
  refine ⟨pullback (t j) s, g, i, hj, inferInstance, inferInstance, inferInstance, ?_⟩
  exact pullback.lift_snd _ _ _

end AlgebraicGeometry.Scheme.FinitePresentationEnvelope.System
