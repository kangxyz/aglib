/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitFunctor
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.QcqsSections
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered

/-! # Explicit index-universe transport for the actual coefficient-colimit cocone

The scheme universe stays fixed. The library's equivalence-based size restriction
transports preservation from the established large-index qcqs theorem.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

/-- Restrict the established qcqs coefficient theorem through the native index-size bridge. -/
abbrev qcqsSectionsPreservesSmallFilteredColimits {S : Scheme.{u}} (U : S.Etale)
    [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    PreservesFilteredColimitsOfSize.{u, u}
      ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)) := by
  let : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      ((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U)) := {
    preserves_filtered_colimits J _ _ := qcqsSectionsPreservesFilteredColimits (I := J) U }
  exact preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _

variable {I : Type u} [Category.{u} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (c : Cocone X) (F : DiagramCoefficientSystem X)

/-- The actual global-section diagram, with the geometry theorem's original small index. -/
def smallConeCoefficientSectionsFunctor : I ⥤ AddCommGrpCat.{u + 1} :=
  coneCoefficientFunctor X c F ⋙ globalSections c.pt.unop

/-- Its original coefficient-colimit cocone. -/
def smallConeCoefficientSectionsCocone : Cocone (smallConeCoefficientSectionsFunctor X c F) :=
  (globalSections c.pt.unop).mapCocone (colimit.cocone (coneCoefficientFunctor X c F))

/-- The actual outer colimit for the small-index geometric theorem. -/
def isColimitSmallConeCoefficientSections [IsFiltered I]
    [CompactSpace c.pt.unop] [QuasiSeparatedSpace c.pt.unop] :
    IsColimit (smallConeCoefficientSectionsCocone X c F) := by
  let : CompactSpace (etaleTerminal c.pt.unop).left := by
    change CompactSpace c.pt.unop
    infer_instance
  let : QuasiSeparatedSpace (etaleTerminal c.pt.unop).left := by
    change QuasiSeparatedSpace c.pt.unop
    infer_instance
  let := qcqsSectionsPreservesSmallFilteredColimits (etaleTerminal c.pt.unop)
  exact isColimitOfPreserves (globalSections c.pt.unop)
    (colimit.isColimit (coneCoefficientFunctor X c F))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
