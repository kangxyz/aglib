/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.System
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.Overlap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered

/-!
# Actual quasi-affine open subsystems of arithmetic approximations

A compact quasi-affine open of the original limit is selected at an actual
stage. The native cofinal base tail and open-restriction diagram retain their
original limits. The overlap cone is transported only along the selected open
equality, so its point is literally the original open scheme. All chart maps
and cartesian comparison squares are retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope

/-- A selected actual stage open realizing a prescribed quasi-affine open of
an arithmetic limit. Its existence is proved below, not assumed as an oracle. -/
structure OpenSubsystem {X : Scheme.{u}} (M : System X) (W : X.Opens) where
  /-- The original stage selected for the open. -/
  index : M.Index
  /-- The actual open at that stage. -/
  stageOpen : (M.diagram.obj index).Opens
  /-- This stage open is quasi-compact. -/
  compact : IsCompact (stageOpen : Set (M.diagram.obj index))
  /-- This stage open is quasi-affine. -/
  quasiAffine : IsQuasiAffine stageOpen.toScheme
  /-- Its original inverse image is the prescribed open. -/
  preimage_eq : M.projection.app index ⁻¹ᵁ stageOpen = W

attribute [instance] OpenSubsystem.quasiAffine

/-- Every prescribed compact quasi-affine open is realized at an actual
stage of the original arithmetic approximation. -/
theorem nonempty_openSubsystem {X : Scheme.{u}} (M : System X) (W : X.Opens)
    (hW : IsCompact (W : Set X)) [IsQuasiAffine W.toScheme] :
    Nonempty (OpenSubsystem M W) := by
  obtain ⟨i, U, hU, he, hq⟩ :=
    exists_quasiAffine_open_preimage_eq M.diagram M.cone M.isLimit W hW
  exact ⟨⟨i, U, hU, hq, he⟩⟩

namespace OpenSubsystem

variable {X : Scheme.{u}} {M : System X} {W : X.Opens} (P : OpenSubsystem M W)

/-- The original small cofiltered tail below the selected stage. -/
abbrev Index := Over P.index

/-- The original arithmetic diagram restricted to the selected tail. -/
@[simps! obj map]
def baseDiagram : P.Index ⥤ Scheme.{u} := Over.forget P.index ⋙ M.diagram

/-- The native whiskered base cone, with its unchanged literal point. -/
@[simps! π_app]
def baseCone : Cone P.baseDiagram := M.cone.whisker (Over.forget P.index)

@[simp] theorem baseCone_pt : P.baseCone.pt = X := rfl

/-- The original base scheme remains the limit of the selected cofinal tail. -/
def baseIsLimit : IsLimit P.baseCone :=
  (Functor.Initial.isLimitWhiskerEquiv (Over.forget P.index) M.cone).symm M.isLimit

instance base_stage_compact (j : P.Index) : CompactSpace (P.baseDiagram.obj j) :=
  M.compact j.left

instance base_stage_finiteType (j : P.Index) :
    LocallyOfFiniteType (specULiftZIsTerminal.from (P.baseDiagram.obj j)) :=
  M.finiteType j.left

instance base_map_isAffineHom {j k : P.Index} (r : j ⟶ k) :
    IsAffineHom (P.baseDiagram.map r) := M.affine r.left

/-- The native diagram of inverse images of the selected stage open. -/
@[simps! obj]
def overlapDiagram : P.Index ⥤ Scheme.{u} :=
  AlgebraicGeometry.opensDiagram M.diagram P.index P.stageOpen

/-- The native open inclusions into the original base tail. -/
@[simps! app]
def inclusion : P.overlapDiagram ⟶ P.baseDiagram :=
  AlgebraicGeometry.opensDiagramι M.diagram P.index P.stageOpen

instance inclusion_isOpenImmersion (j : P.Index) : IsOpenImmersion (P.inclusion.app j) :=
  inferInstanceAs (IsOpenImmersion
    ((AlgebraicGeometry.opensDiagramι M.diagram P.index P.stageOpen).app j))

instance overlap_map_isAffineHom {j k : P.Index} (r : j ⟶ k) :
    IsAffineHom (P.overlapDiagram.map r) :=
  inferInstanceAs (IsAffineHom
    ((AlgebraicGeometry.opensDiagram M.diagram P.index P.stageOpen).map r))

instance overlap_stage_quasiAffine (j : P.Index) : IsQuasiAffine (P.overlapDiagram.obj j) := by
  have : IsAffineHom (M.diagram.map j.hom ∣_ P.stageOpen) :=
    IsZariskiLocalAtTarget.restrict (P := @IsAffineHom) (M.affine j.hom) P.stageOpen
  exact IsQuasiAffine.of_isAffineHom (M.diagram.map j.hom ∣_ P.stageOpen)

instance overlap_stage_finiteType (j : P.Index) :
    LocallyOfFiniteType (specULiftZIsTerminal.from (P.overlapDiagram.obj j)) := by
  have he : specULiftZIsTerminal.from (P.overlapDiagram.obj j) =
      P.inclusion.app j ≫ specULiftZIsTerminal.from (P.baseDiagram.obj j) :=
    specULiftZIsTerminal.hom_ext _ _
  rw [he]
  infer_instance

/-- The selected equality changes only the overlap cone point to the literal
original open scheme; all its projections are the native restrictions. -/
def overlapCone : Cone P.overlapDiagram :=
  (AlgebraicGeometry.opensCone M.diagram M.cone P.index P.stageOpen).extend
    (X.isoOfEq P.preimage_eq).inv

@[simp] theorem overlapCone_pt : P.overlapCone.pt = W.toScheme := rfl

/-- The literal original open scheme is the limit of the native open diagram. -/
def overlapIsLimit : IsLimit P.overlapCone :=
  (AlgebraicGeometry.isLimitOpensCone M.diagram M.cone M.isLimit P.index P.stageOpen).ofIsoLimit
    ((AlgebraicGeometry.opensCone M.diagram M.cone P.index P.stageOpen).extendIso
      (X.isoOfEq P.preimage_eq))

/-- Original overlap projections commute with the unchanged base inclusion. -/
@[reassoc (attr := simp)]
theorem overlapCone_π_inclusion (j : P.Index) :
    P.overlapCone.π.app j ≫ P.inclusion.app j = W.ι ≫ P.baseCone.π.app j := by
  simp [overlapCone, inclusion, baseCone, AlgebraicGeometry.opensCone, System.cone]

/-- Every transition square of the original open-inclusion diagram is
cartesian. No separate replacement of the overlap diagram is used. -/
theorem inclusion_equifibered : P.inclusion.Equifibered := by
  intro j k r
  apply IsOpenImmersion.isPullback (P.overlapDiagram.map r) (P.inclusion.app j)
    (P.inclusion.app k) (P.baseDiagram.map r) (P.inclusion.naturality r).symm
  simp only [inclusion, AlgebraicGeometry.opensDiagramι_app, Opens.opensRange_ι]
  change M.diagram.map r.left ⁻¹ᵁ (M.diagram.map k.hom ⁻¹ᵁ P.stageOpen) =
    M.diagram.map j.hom ⁻¹ᵁ P.stageOpen
  rw [← Hom.comp_preimage, ← M.diagram.map_comp, Over.w r]

/-- Each original overlap-to-stage square is cartesian after the literal
open equality transports the cone point. -/
theorem cone_isPullback (j : P.Index) :
    IsPullback (P.overlapCone.π.app j) W.ι (P.inclusion.app j) (P.baseCone.π.app j) := by
  apply IsOpenImmersion.isPullback (P.overlapCone.π.app j) W.ι
    (P.inclusion.app j) (P.baseCone.π.app j) (P.overlapCone_π_inclusion j).symm
  simp only [inclusion, AlgebraicGeometry.opensDiagramι_app, Opens.opensRange_ι]
  change M.projection.app j.left ⁻¹ᵁ (M.diagram.map j.hom ⁻¹ᵁ P.stageOpen) = W
  have hcomm : M.projection.app j.left ≫ M.diagram.map j.hom =
      M.projection.app P.index := M.cone.w j.hom
  rw [← Hom.comp_preimage, hcomm]
  exact P.preimage_eq

/-- The selected tail is itself an actual arithmetic system on the unchanged
original base scheme. -/
def baseSystem : System X where
  Index := P.Index
  category := inferInstance
  cofiltered := inferInstance
  diagram := P.baseDiagram
  projection := P.baseCone.π
  isLimit := P.baseIsLimit
  affine _ := inferInstance
  finiteType _ := inferInstance
  compact _ := inferInstance

/-- The selected open diagram is an actual arithmetic system on the literal
original overlap, retaining all its native open inclusions. -/
def overlapSystem : System W.toScheme where
  Index := P.Index
  category := inferInstance
  cofiltered := inferInstance
  diagram := P.overlapDiagram
  projection := P.overlapCone.π
  isLimit := P.overlapIsLimit
  affine _ := inferInstance
  finiteType _ := inferInstance
  compact _ := inferInstance

end OpenSubsystem
end AlgebraicGeometry.Scheme.FinitePresentationEnvelope
