/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.PreparedOverlap
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.SubalgebraGluing

/-!
# Actual affine-coordinate approximation from the prepared overlap

The original affine chart is the colimit of the native pullback rings. The
chosen denominator pairs make the original overlap maps open with their exact
principal images. Eligible finite subalgebras and native binary gluing then
construct the original coordinate pushout's arithmetic approximation system.
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

/-- The actual rings pairing the original affine chart with the overlap stages. -/
def ringDiagram : P.Indexᵒᵖ ⥤ CommRingCat.{u} :=
  CommRingCat.FilteredPullback.ringDiagram P.sectionCone P.sectionMap

/-- The first projections have the original affine coordinate ring as cocone point. -/
def ringCone : Cocone P.ringDiagram :=
  CommRingCat.FilteredPullback.ringCocone P.sectionCone P.sectionMap

/-- The native pullback-ring cocone is an actual filtered colimit. -/
def ringIsColimit : IsColimit P.ringCone :=
  CommRingCat.FilteredPullback.ringCoconeIsColimit P.sectionCone P.sectionMap P.sectionIsColimit

/-- The original denominator pairs have exactly matching global-section values. -/
theorem section_pair (i : P.Index) (l : P.Denominator) :
    P.sectionMap.hom (P.original l) =
      (P.sectionCone.ι.app (op i)).hom (P.stageSections i l) :=
  (P.stageSections_projection i l).symm

/-- The actual denominator elements of each pullback ring. -/
def denominator (i : P.Indexᵒᵖ) (l : P.Denominator) : P.ringDiagram.obj i :=
  OverlapPullback.denominator P.sectionDiagram P.sectionCone P.sectionMap
    P.original P.stageSections P.section_pair i.unop l

/-- Denominator elements commute with the actual filtered ring transitions. -/
theorem denominator_naturality {i j : P.Indexᵒᵖ} (f : i ⟶ j) (l : P.Denominator) :
    (P.ringDiagram.map f).hom (P.denominator i l) = P.denominator j l :=
  OverlapPullback.denominator_naturality P.sectionDiagram P.sectionCone P.sectionMap
    P.original P.stageSections P.section_pair P.stageSections_naturality f.unop l

/-- The native affinization maps of the unchanged overlap stages. -/
def affinization : P.overlapSystem.diagram ⟶ P.sectionDiagram.rightOp ⋙ Scheme.Spec :=
  OverlapPullback.affinization P.overlapSystem.diagram

instance affinization_isOpenImmersion (i : P.Index) : IsOpenImmersion (P.affinization.app i) :=
  inferInstanceAs (IsOpenImmersion (P.overlapSystem.diagram.obj i).toSpecΓ)

/-- The original overlap maps composed with the native second ring projections. -/
def toAffine : P.overlapSystem.diagram ⟶ P.ringDiagram.rightOp ⋙ Scheme.Spec :=
  OverlapPullback.toAffine P.sectionDiagram P.sectionCone P.sectionMap
    P.overlapSystem.diagram P.affinization

instance toAffine_isOpenImmersion (i : P.Index) : IsOpenImmersion (P.toAffine.app i) :=
  OverlapPullback.toAffine_isOpenImmersion P.sectionDiagram P.sectionCone P.sectionMap
    P.original P.stageSections P.section_pair P.overlapSystem.diagram P.affinization
    P.stageSections_opensRange P.localized i

/-- The actual pullback-ring overlap image is the specified union of principal opens. -/
theorem toAffine_opensRange (i : P.Index) :
    (P.toAffine.app i).opensRange = ⨆ l, PrimeSpectrum.basicOpen (P.denominator (op i) l) := by
  have : IsOpenImmersion ((OverlapPullback.toAffine P.sectionDiagram P.sectionCone P.sectionMap
      P.overlapSystem.diagram P.affinization).app i) := P.toAffine_isOpenImmersion i
  exact OverlapPullback.toAffine_opensRange P.sectionDiagram P.sectionCone P.sectionMap
    P.original P.stageSections P.section_pair P.overlapSystem.diagram P.affinization
    P.stageSections_opensRange P.localized i

/-- The original overlap cone and the literal affine-coordinate cocone commute. -/
theorem affine_cone (i : P.Index) :
    P.overlapSystem.projection.app i ≫ P.toAffine.app i =
      (OpenUnionCoordinates.image U V).ι ≫ Spec.map (P.ringCone.ι.app (op i)) := by
  exact (OverlapPullback.cone_square_commutes P.sectionDiagram P.sectionCone P.sectionMap
    P.overlapSystem.diagram P.affinization
    (OpenUnionCoordinates.image U V).toScheme.toSpecΓ (OpenUnionCoordinates.image U V).ι
    (OpenPrincipalLocalization.toSpecΓ_sectionMap Γ(U.toScheme, ⊤)
      (OpenUnionCoordinates.image U V)).symm i (P.overlapSystem.projection.app i)
    (OverlapPullback.affinization_cone_square P.overlapSystem.diagram
      P.overlapSystem.cone i)).symm

/-- Pulling the denominator pairs to the original ring recovers the original open image. -/
theorem original_opensRange (i : P.Index) :
    (OpenUnionCoordinates.image U V).ι.opensRange =
      ⨆ l, PrimeSpectrum.basicOpen ((P.ringCone.ι.app (op i)).hom (P.denominator (op i) l)) := by
  rw [Opens.opensRange_ι]
  exact P.originalCover.trans (OverlapPullback.denominator_principal_fst
    P.sectionDiagram P.sectionCone P.sectionMap P.original P.stageSections P.section_pair i).symm

/-- All actual geometric and ring suppliers assemble an arithmetic system on
the original coordinate pushout. No overlap model is supplied as an oracle. -/
def gluedSystem : System (pushout (OpenUnionCoordinates.image U V).ι
    (OpenUnionCoordinates.toRight U V)) :=
  SubalgebraGluing.system P.ringDiagram P.overlapSystem.diagram P.rightSystem.diagram
    P.toAffine P.inclusion P.inclusion_equifibered P.denominator P.denominator_naturality
    P.toAffine_opensRange P.ringCone P.ringIsColimit P.overlapSystem.cone P.rightSystem.cone
    P.rightSystem.isLimit (OpenUnionCoordinates.image U V).ι (OpenUnionCoordinates.toRight U V)
    P.affine_cone P.original_opensRange P.inclusion_cone_isPullback

/-- The actual open-union pushout comparison restores the literal original source. -/
def originalSystem (hcover : U ⊔ V = ⊤) : System X :=
  P.gluedSystem.ofIso (OpenUnionCoordinates.isPushout U V hcover).isoPushout

end AlgebraicGeometry.Scheme.FinitePresentationEnvelope.OverlapPreparation
