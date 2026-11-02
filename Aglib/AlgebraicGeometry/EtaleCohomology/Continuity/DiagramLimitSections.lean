/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitFunctor
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.QcqsSections
public import Aglib.CategoryTheory.Filtered.CoefficientSections

/-! # The actual outer coefficient-colimit cocone on a scheme cone point

This supplies the outer colimit in the two-step compatible-system argument.
It does not assert the independent fixed-coefficient scheme-tail continuity.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge

section Data

variable {I : Type uI} [Category.{vI} I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (F : DiagramCoefficientSystem X)

/-- Original global sections of the one actual pulled-back coefficient diagram. -/
def coneCoefficientSectionsFunctor : I ⥤ AddCommGrpCat.{u + 1} :=
  (diagramConeAdjunctionData X c).coefficientSectionsFunctor F (globalSections c.pt.unop)

/-- The whole original section map is the section image of the same coefficient map. -/
theorem coneCoefficientSectionsFunctor_map {i j : I} (a : i ⟶ j) :
    (coneCoefficientSectionsFunctor X c F).map a =
      (globalSections c.pt.unop).map (coneCoefficientMap X c F a) := rfl

variable [HasColimit (coneCoefficientFunctor X c F)]

/-- The original colimit coefficient, with actual existence kept explicit at arbitrary size. -/
abbrev coneCoefficientColimit : AbelianSheaf.{u, u + 1} c.pt.unop :=
  colimit (coneCoefficientFunctor X c F)

/-- The SAME original coefficient-colimit section cocone. -/
def coneCoefficientSectionsCocone : Cocone (coneCoefficientSectionsFunctor X c F) := by
  let : HasColimit ((diagramConeAdjunctionData X c).coefficientFunctor F) :=
    inferInstanceAs (HasColimit (coneCoefficientFunctor X c F))
  exact (diagramConeAdjunctionData X c).coefficientSectionsCocone F
    (globalSections c.pt.unop)

/-- Every original insertion retains its exact section-image value. -/
theorem coneCoefficientSectionsCocone_ι (i : I) :
    (coneCoefficientSectionsCocone X c F).ι.app i =
      (globalSections c.pt.unop).map (colimit.ι (coneCoefficientFunctor X c F) i) := rfl

end Data

variable {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (F : DiagramCoefficientSystem X)

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
