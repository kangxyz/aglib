/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.System

/-!
# Transport of actual arithmetic approximation systems

Transport along an isomorphism changes only the literal limiting scheme and its projections.
The small index, actual diagram, transition maps, and arithmetic finiteness certificates are
retained unchanged. The universal property is transported with the supplied isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope.System

variable {X Y : Scheme.{u}}

/-- Transport an actual arithmetic system to an isomorphic literal limiting scheme. -/
def ofIso (M : System X) (e : Y ≅ X) : System Y where
  Index := M.Index
  category := M.category
  cofiltered := M.cofiltered
  diagram := M.diagram
  projection := (Functor.const M.Index).map e.hom ≫ M.projection
  isLimit := M.isLimit.ofIsoLimit ((Cone.mk X M.projection).extendIso e.symm)
  affine := M.affine
  finiteType := M.finiteType
  compact := M.compact

/-- Transport does not replace the stages or transition maps. -/
@[simp] theorem ofIso_diagram (M : System X) (e : Y ≅ X) :
    (M.ofIso e).diagram = M.diagram := rfl

/-- Every transported projection is the original isomorphism followed by the original map. -/
@[simp] theorem ofIso_projection_app (M : System X) (e : Y ≅ X) (i : M.Index) :
    (M.ofIso e).projection.app i = e.hom ≫ M.projection.app i := rfl

end AlgebraicGeometry.Scheme.FinitePresentationEnvelope.System
