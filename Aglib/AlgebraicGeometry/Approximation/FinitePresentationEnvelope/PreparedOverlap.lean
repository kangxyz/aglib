/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.OverlapPreparation
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.OverlapTail
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.SystemTransport
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.SystemReindex
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.OverlapPullback

/-!
# The actual prepared overlap tail

The chosen principal stage determines a cofinal tail of both original chart
systems. Its overlap point is the literal open image in the affine spectrum;
the other point is the original second chart. Native sections, inclusion maps,
cartesian squares, and the section-ring colimit are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope.OverlapPreparation

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} {U V : X.Opens} [IsAffine U.toScheme]
  {M : System V.toScheme} (P : OverlapPreparation U V M)

/-- The actual tail below the chosen principal stage. -/
abbrev Index := Over P.stage

/-- The original second chart and its selected arithmetic tail. -/
def rightSystem : System V.toScheme :=
  P.subsystem.baseSystem.reindex (Over.forget P.stage)

/-- The original overlap image and its selected arithmetic tail. -/
def overlapSystem : System (OpenUnionCoordinates.image U V).toScheme :=
  (P.subsystem.overlapSystem.ofIso (OpenUnionCoordinates.overlapIso U V).symm).reindex
    (Over.forget P.stage)

instance overlap_stage_quasiAffine (j : P.Index) :
    IsQuasiAffine (P.overlapSystem.diagram.obj j) :=
  inferInstanceAs (IsQuasiAffine (P.subsystem.overlapDiagram.obj j.left))

/-- The actual reindexed open inclusions into the second chart stages. -/
def inclusion : P.overlapSystem.diagram ⟶ P.rightSystem.diagram :=
  Functor.whiskerLeft (Over.forget P.stage) P.subsystem.inclusion

instance inclusion_isOpenImmersion (j : P.Index) : IsOpenImmersion (P.inclusion.app j) :=
  inferInstanceAs (IsOpenImmersion (P.subsystem.inclusion.app j.left))

/-- Reindexing preserves the actual cartesian open overlap squares. -/
theorem inclusion_equifibered : P.inclusion.Equifibered := by
  intro j k f
  exact P.subsystem.inclusion_equifibered f.left

/-- The literal overlap image maps to the original second chart. -/
@[reassoc (attr := simp)]
theorem inclusion_cone (j : P.Index) :
    P.overlapSystem.projection.app j ≫ P.inclusion.app j =
      OpenUnionCoordinates.toRight U V ≫ P.rightSystem.projection.app j := by
  change ((OpenUnionCoordinates.overlapIso U V).inv ≫
      P.subsystem.overlapCone.π.app j.left) ≫ P.subsystem.inclusion.app j.left =
    ((OpenUnionCoordinates.overlapIso U V).inv ≫ (OpenUnionCoordinates.overlap U V).ι) ≫
      P.subsystem.baseCone.π.app j.left
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f : (OpenUnionCoordinates.overlap U V).toScheme ⟶
        M.diagram.obj j.left.left ↦ (OpenUnionCoordinates.overlapIso U V).inv ≫ f)
      (P.subsystem.overlapCone_π_inclusion j.left)).trans
        (Category.assoc _ _ _).symm)

/-- The original second-chart cone squares remain cartesian after the actual
image isomorphism and the cofinal tail are applied. -/
theorem inclusion_cone_isPullback (j : P.Index) :
    IsPullback (P.overlapSystem.projection.app j) (OpenUnionCoordinates.toRight U V)
      (P.inclusion.app j) (P.rightSystem.projection.app j) := by
  change IsPullback ((OpenUnionCoordinates.overlapIso U V).inv ≫
      P.subsystem.overlapCone.π.app j.left)
    ((OpenUnionCoordinates.overlapIso U V).inv ≫ (OpenUnionCoordinates.overlap U V).ι)
    (P.subsystem.inclusion.app j.left) (P.subsystem.baseCone.π.app j.left)
  apply (P.subsystem.cone_isPullback j.left).of_iso
    (OpenUnionCoordinates.overlapIso U V) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  all_goals simp

/-- The same chosen sections at every actual later overlap stage. -/
def stageSections (j : P.Index) (l : P.Denominator) :
    Γ(P.overlapSystem.diagram.obj j, ⊤) :=
  tailSections P.subsystem.overlapDiagram P.stage P.stageSection j l

/-- Naturality of the specified denominators on the actual tail. -/
theorem stageSections_naturality {j k : P.Index} (f : j ⟶ k) (l : P.Denominator) :
    (P.overlapSystem.diagram.map f).appTop (P.stageSections k l) = P.stageSections j l :=
  tailSections_naturality P.subsystem.overlapDiagram P.stage P.stageSection f l

/-- The original global sections are still the exact values of the tail denominators. -/
theorem stageSections_projection (j : P.Index) (l : P.Denominator) :
    (P.overlapSystem.projection.app j).appTop (P.stageSections j l) =
      (OpenPrincipalLocalization.sectionMap Γ(U.toScheme, ⊤)
        (OpenUnionCoordinates.image U V)).hom (P.original l) :=
  (tailSections_projection P.subsystem.overlapDiagram P.stage P.stageSection
    (overlapImageCone U V M P.subsystem) j l).trans (P.section_eq l)

/-- Every later overlap retains the exact chosen principal image. -/
theorem stageSections_opensRange (j : P.Index) :
    (P.overlapSystem.diagram.obj j).toSpecΓ.opensRange =
      ⨆ l, PrimeSpectrum.basicOpen (P.stageSections j l) :=
  tailSections_opensRange P.subsystem.overlapDiagram P.stage P.stageSection P.stageImage j

/-- The actual ring diagram of global sections of the overlap tail. -/
def sectionDiagram : P.Indexᵒᵖ ⥤ CommRingCat.{u} := P.overlapSystem.diagram.op ⋙ Scheme.Γ

/-- Its original cocone, at the global sections of the original overlap image. -/
def sectionCone : Cocone P.sectionDiagram :=
  OverlapPullback.sectionCocone P.overlapSystem.diagram P.overlapSystem.cone

/-- Affine-transition qcqs limits give the actual global-section colimit. -/
def sectionIsColimit : IsColimit P.sectionCone :=
  (AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone P.overlapSystem.diagram
    P.overlapSystem.cone P.overlapSystem.isLimit).some

/-- The literal map from the original affine chart to the overlap sections. -/
def sectionMap : Γ(U.toScheme, ⊤) ⟶ P.sectionCone.pt :=
  OpenPrincipalLocalization.sectionMap Γ(U.toScheme, ⊤) (OpenUnionCoordinates.image U V)

end AlgebraicGeometry.Scheme.FinitePresentationEnvelope.OverlapPreparation
