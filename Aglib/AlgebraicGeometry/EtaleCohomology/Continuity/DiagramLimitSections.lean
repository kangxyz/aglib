/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitFunctor
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.QcqsSections

/-! # The actual outer coefficient-colimit cocone on a scheme cone point

This supplies the outer colimit in the two-step compatible-system argument.
It does not assert the independent fixed-coefficient scheme-tail continuity.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

variable {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (F : DiagramCoefficientSystem X)

/-- The original colimit coefficient of the actual pulled-back system. -/
abbrev coneCoefficientColimit : AbelianSheaf.{u, u + 1} c.pt.unop :=
  colimit (coneCoefficientFunctor X c F)

/-- Original global sections of every pulled-back stage coefficient. -/
def coneCoefficientSectionsFunctor : I ⥤ AddCommGrpCat.{u + 1} :=
  coneCoefficientFunctor X c F ⋙ globalSections c.pt.unop

/-- The actual coefficient-colimit section cocone. -/
def coneCoefficientSectionsCocone : Cocone (coneCoefficientSectionsFunctor X c F) :=
  (globalSections c.pt.unop).mapCocone (colimit.cocone (coneCoefficientFunctor X c F))

/-- The fixed-qcqs coefficient theorem proves this outer cocone is a colimit. -/
def isColimitConeCoefficientSections [CompactSpace c.pt.unop] [QuasiSeparatedSpace c.pt.unop] :
    IsColimit (coneCoefficientSectionsCocone X c F) := by
  let : CompactSpace (etaleTerminal c.pt.unop).left := by
    change CompactSpace c.pt.unop
    infer_instance
  let : QuasiSeparatedSpace (etaleTerminal c.pt.unop).left := by
    change QuasiSeparatedSpace c.pt.unop
    infer_instance
  let := qcqsSectionsPreservesFilteredColimits (I := I) (etaleTerminal c.pt.unop)
  exact isColimitOfPreserves (globalSections c.pt.unop)
    (colimit.isColimit (coneCoefficientFunctor X c F))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
