/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.ClosedSubscheme.Ideals
public import Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.FinitePresentationApproximation
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Finitely presented closed-subscheme approximation over the original ambient

The native closed-immersion approximation supplies the actual scheme diagram,
its original source as cone point, and the original structural triangle.
Lifting that cone to the over category gives the interface used by proper
approximation. Finite-type ideals and the limiting proof have one native owner.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A finite-type ideal defines a finitely presented closed immersion. -/
theorem locallyOfFinitePresentation_subschemeι {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (hI : I.IsFiniteType) : LocallyOfFinitePresentation I.subschemeι :=
  I.locallyOfFinitePresentation_subschemeι_iff.mpr hI

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Approximation.ClosedSubscheme

variable {X Y : Scheme.{u}}

/-- The native cofiltered index of finite-type subideals of the original kernel. -/
abbrev FinitePresentationIndex (f : X ⟶ Y) := f.ker.FiniteTypeSubidealᵒᵖ

instance finitePresentationIndex_isCofiltered (f : X ⟶ Y) :
    IsCofiltered (FinitePresentationIndex f) := inferInstance

/-- The contravariant native finite-type subideal diagram. -/
abbrev finitePresentationIdealDiagram (f : X ⟶ Y) :
    FinitePresentationIndex f ⥤ Y.IdealSheafDataᵒᵖ :=
  (Scheme.IdealSheafData.finiteTypeSubidealForget f.ker).op

/-- The native scheme diagram equipped with its original ambient structure maps. -/
abbrev finitePresentationDiagram (f : X ⟶ Y) : FinitePresentationIndex f ⥤ Over Y :=
  Over.lift f.finitePresentationApproximationDiagram f.finitePresentationApproximationStructure

instance finitePresentationDiagram_obj_finitePresentation (f : X ⟶ Y)
    (J : FinitePresentationIndex f) :
    LocallyOfFinitePresentation ((finitePresentationDiagram f).obj J).hom := by
  change LocallyOfFinitePresentation (f.finitePresentationApproximationStructure.app J)
  infer_instance

instance finitePresentationDiagram_obj_closed (f : X ⟶ Y)
    (J : FinitePresentationIndex f) :
    IsClosedImmersion ((finitePresentationDiagram f).obj J).hom := by
  change IsClosedImmersion (f.finitePresentationApproximationStructure.app J)
  infer_instance

instance finitePresentationDiagram_map_closed (f : X ⟶ Y)
    {J K : FinitePresentationIndex f} (a : J ⟶ K) :
    IsClosedImmersion ((finitePresentationDiagram f).map a).left := by
  change IsClosedImmersion (f.finitePresentationApproximationDiagram.map a)
  infer_instance

/-- The native finite-type subideals have supremum the original kernel. -/
theorem iSup_finitePresentationIdealDiagram [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) : (⨆ J, ((finitePresentationIdealDiagram f).obj J).unop) = f.ker := by
  change (⨆ J : f.ker.FiniteTypeSubidealᵒᵖ, J.unop.val) = f.ker
  apply le_antisymm
  · exact iSup_le fun J => J.unop.property.1
  · exact f.ker.iSup_finiteTypeSubideal.ge.trans (iSup_le fun J =>
      le_iSup (fun K : f.ker.FiniteTypeSubidealᵒᵖ => K.unop.val) (op J))

/-- The lifted native cone has the original arrow as its literal point. -/
def finitePresentationCone (f : X ⟶ Y) : Cone (finitePresentationDiagram f) :=
  Over.liftCone f.finitePresentationApproximationDiagram
    f.finitePresentationApproximationStructure f.finitePresentationApproximationCone f
    (fun J => f.finitePresentationApproximationCone_comp J)

/-- Native closed-immersion approximation supplies the over-category limit. -/
def isLimitFinitePresentationCone [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsClosedImmersion f] : IsLimit (finitePresentationCone f) :=
  Over.isLimitLiftCone f.finitePresentationApproximationDiagram
    f.finitePresentationApproximationStructure f.finitePresentationApproximationCone f
    (fun J => f.finitePresentationApproximationCone_comp J)
    f.finitePresentationApproximationConeIsLimit

/-- The original scheme cone, with only its ambient structure forgotten. -/
def finitePresentationSchemeCone (f : X ⟶ Y) :
    Cone (finitePresentationDiagram f ⋙ Over.forget Y) :=
  (Over.forget Y).mapCone (finitePresentationCone f)

/-- The original source is the native limit of its finitely presented closed approximants. -/
def isLimitFinitePresentationSchemeCone [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsClosedImmersion f] : IsLimit (finitePresentationSchemeCone f) := by
  have : IsConnected (FinitePresentationIndex f) := IsCofiltered.isConnected _
  exact isLimitOfPreserves (Over.forget Y) (isLimitFinitePresentationCone f)

instance finitePresentationCone_projection_closed
    (f : X ⟶ Y) [IsClosedImmersion f] (J : FinitePresentationIndex f) :
    IsClosedImmersion ((finitePresentationCone f).π.app J).left := by
  change IsClosedImmersion (f.finitePresentationApproximationCone.π.app J)
  infer_instance

/-- The limiting point is definitionally the original arrow over the ambient scheme. -/
theorem finitePresentationCone_pt (f : X ⟶ Y) :
    (finitePresentationCone f).pt = Over.mk f := rfl

end AlgebraicGeometry.Approximation.ClosedSubscheme
