/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Noetherian
/-!
# Actual finite local presentations of global coherent sheaves

The affine-chart coherent condition produces finite presentations on the
actual cover by affine opens. These are transported to the over-site by the
proved scheme sheaf equivalences. Thus the global category consists of actual
finitely presented sheaves, and in particular actual quasicoherent sheaves.
The finite-presentation equivalence below retains local Noetherianity.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Modules.Coherent

instance coherent_obj_finitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : FiniteTypeSheaves X) : M.obj.IsFinitePresentation :=
      affineLocallyFiniteType_finitePresentation M.property

instance coherent_obj_quasicoherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : FiniteTypeSheaves X) : M.obj.IsQuasicoherent := by
  have := coherent_obj_finitePresentation M
  infer_instance

/-- The actual inclusion of global coherent sheaves into finitely presented
sheaves. The proof above supplies its required object property. -/
def coherentToFinitePresentation (X : Scheme.{u}) [IsLocallyNoetherian X] :
    FiniteTypeSheaves X ⥤ Scheme.Modules.FinitePresentation X :=
  (Scheme.Modules.finitePresentation X).lift (finiteTypeSheavesToModules X)
    (fun M => affineLocallyFiniteType_finitePresentation M.property)

/-- On a locally noetherian scheme the two actual notions agree. -/
theorem affineLocallyFiniteType_iff_finitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) : affineLocallyFiniteType X M ↔ M.IsFinitePresentation :=
  ⟨affineLocallyFiniteType_finitePresentation, fun h => by
    let := h
    exact affineLocallyFiniteType_of_finitePresentation M⟩


/-- Coherence is local for actual restrictions to a binary open cover. -/
theorem affineLocallyFiniteType_of_binary_openCover {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) (W V : X.Opens) (hWV : W ⊔ V = ⊤)
    (hW : affineLocallyFiniteType W.toScheme (M.restrict W.ι))
    (hV : affineLocallyFiniteType V.toScheme (M.restrict V.ι)) : affineLocallyFiniteType X M := by
  have hW' := affineLocallyFiniteType_finitePresentation hW
  have hV' := affineLocallyFiniteType_finitePresentation hV
  let U : ULift.{u} Bool → X.Opens := fun i => if i.down then W else V
  have hc : IsOpenCover U := by
    rw [IsOpenCover]
    simpa [U, iSup_bool_eq, sup_comm] using hWV
  have : M.IsFinitePresentation := finitePresentation_of_openCover M U hc (by
    intro i
    rcases i with ⟨_ | _⟩ <;> simpa [U] using (by assumption))
  exact affineLocallyFiniteType_of_finitePresentation M


end AlgebraicGeometry.Scheme.Modules.Coherent
