/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.OpenSubsystem
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.OpenUnionCoordinates
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.OpenPrincipalLocalization
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.OverlapPresentation

/-!
# Constructing the finite denominator data for one-affine extension

The overlap is first selected at a quasi-affine arithmetic stage. Its original
open image in the affine chart then supplies finitely many denominators, which
are lifted to a stage with exactly the same principal-image presentation.
All of this data is constructed from the original two opens and actual system.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} (U V : X.Opens) [IsAffine U.toScheme]
  (M : System V.toScheme)

/-- The overlap cone expressed at its literal open image in the affine spectrum. -/
def overlapImageCone (P : OpenSubsystem M (OpenUnionCoordinates.overlap U V)) :
    Cone P.overlapDiagram :=
  P.overlapCone.extend (OpenUnionCoordinates.overlapIso U V).inv

/-- The specified image is the actual limit of the unchanged overlap diagram. -/
def overlapImageIsLimit (P : OpenSubsystem M (OpenUnionCoordinates.overlap U V)) :
    IsLimit (overlapImageCone U V M P) :=
  P.overlapIsLimit.ofIsoLimit (P.overlapCone.extendIso
    (OpenUnionCoordinates.overlapIso U V))

/-- Actual overlap, selected stage and finite denominators for the affine extension. -/
structure OverlapPreparation where
  /-- The original overlap realized at an actual arithmetic stage. -/
  subsystem : OpenSubsystem M (OpenUnionCoordinates.overlap U V)
  /-- A later stage supporting the chosen principal-image presentation. -/
  stage : subsystem.Index
  /-- The finite family retains the original scheme universe. -/
  Denominator : Type u
  /-- The family is genuinely finite. -/
  [finite : Fintype Denominator]
  /-- Denominators in the original affine chart. -/
  original : Denominator → Γ(U.toScheme, ⊤)
  /-- Matching actual global sections at the selected overlap stage. -/
  stageSection : Denominator → Γ(subsystem.overlapDiagram.obj stage, ⊤)
  /-- The original overlap image is covered by the specified principal opens. -/
  originalCover : OpenUnionCoordinates.image U V =
    ⨆ l, PrimeSpectrum.basicOpen (original l)
  /-- The original map to overlap sections is invertible on these localizations. -/
  localized : ∀ l, Function.Bijective (Localization.awayMap
    (OpenPrincipalLocalization.sectionMap Γ(U.toScheme, ⊤)
      (OpenUnionCoordinates.image U V)).hom (original l))
  /-- The selected sections restrict to exactly the original denominators. -/
  section_eq : ∀ l, ((overlapImageCone U V M subsystem).π.app stage).appTop (stageSection l) =
    (OpenPrincipalLocalization.sectionMap Γ(U.toScheme, ⊤)
      (OpenUnionCoordinates.image U V)).hom (original l)
  /-- The selected stage has precisely the indicated principal image. -/
  stageImage : (subsystem.overlapDiagram.obj stage).toSpecΓ.opensRange =
    ⨆ l, PrimeSpectrum.basicOpen (stageSection l)

attribute [instance] OverlapPreparation.finite

/-- Construct the actual finite overlap preparation from the original affine
chart, compact second chart, and its arithmetic approximation. -/
theorem nonempty_overlapPreparation [QuasiSeparatedSpace X]
    (hV : IsCompact (V : Set X)) : Nonempty (OverlapPreparation U V M) := by
  have : IsQuasiAffine (OpenUnionCoordinates.overlap U V).toScheme :=
    OpenUnionCoordinates.overlap_isQuasiAffine U V hV
  obtain ⟨P⟩ := nonempty_openSubsystem M (OpenUnionCoordinates.overlap U V)
    (OpenUnionCoordinates.overlap_isCompact U V hV)
  let Q := OpenUnionCoordinates.image U V
  have hQ : IsCompact (Q : Set (Spec Γ(U.toScheme, ⊤))) :=
    OpenUnionCoordinates.image_isCompact U V hV
  have : CompactSpace Q.toScheme := isCompact_iff_compactSpace.mp hQ
  have : IsQuasiAffine Q.toScheme := IsQuasiAffine.of_isImmersion Q.ι
  obtain ⟨L, hL, g, hg, hloc, -, himage⟩ :=
    OpenPrincipalLocalization.exists_finite_principal_cover Γ(U.toScheme, ⊤) Q hQ
  let := hL
  have : IsQuasiAffine (overlapImageCone U V M P).pt :=
    inferInstanceAs (IsQuasiAffine Q.toScheme)
  obtain ⟨i, t, ht, hi⟩ := exists_principal_image_at_stage P.overlapDiagram
    (overlapImageCone U V M P) (overlapImageIsLimit U V M P)
    (fun l ↦ (OpenPrincipalLocalization.sectionMap Γ(U.toScheme, ⊤) Q).hom (g l)) himage
  exact ⟨
    { subsystem := P
      stage := i
      Denominator := L
      finite := hL
      original := g
      stageSection := t
      originalCover := hg
      localized := hloc
      section_eq := ht
      stageImage := hi }⟩

end AlgebraicGeometry.Scheme.FinitePresentationEnvelope
