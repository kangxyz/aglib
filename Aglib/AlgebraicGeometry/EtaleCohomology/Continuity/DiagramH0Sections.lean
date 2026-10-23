/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramCohomologyCocone
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramNativeCocone
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.CoefficientDegreeZero

/-! # Original degree-zero scheme-system cocones from section cocones

The original cohomology groups and section groups have independent universes.
Their native universe lifts are compared through the existing degree-zero
cohomology equivalence, including the original scheme pullback and coefficient
maps. A supplied colimit certificate for the actual section cocone is preserved
by its lift and reflected through the fully faithful lift of original cohomology.
No target colimit, continuity theorem, or invertibility premise is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u e uI vI

attribute [local instance] hasSheafifyLarge

/-- The existing lifted degree-zero equivalence respects the original pullback
followed by its actual coefficient map. -/
lemma cohomologyTransfer_zero_sectionsUlift {X Y : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    (f : Y ⟶ X) {F : AbelianSheaf.{u, u + 1} X}
    {G : AbelianSheaf.{u, u + 1} Y} (φ : (inverseImage f).obj F ⟶ G) :
    AddCommGrpCat.uliftFunctor.{u + 1, e}.map (cohomologyTransfer f φ 0) ≫
        ((Sheaf.H.degreeZeroSectionsUliftIso (etaleTerminalIsTerminal Y)).app G).hom =
      ((Sheaf.H.degreeZeroSectionsUliftIso (etaleTerminalIsTerminal X)).app F).hom ≫
        AddCommGrpCat.uliftFunctor.{e, u + 1}.map (sectionTransfer f φ) := by
  apply AddCommGrpCat.ext
  intro x
  apply ULift.ext
  change Sheaf.H.equiv₀ G (etaleTerminalIsTerminal Y)
      (Sheaf.H.map φ 0 (cohomologyPullback f F 0 x.down)) =
    (globalSections Y).map φ (globalSectionsPullback f F
      (Sheaf.H.equiv₀ F (etaleTerminalIsTerminal X) x.down))
  rw [← Sheaf.H.equiv₀_naturality, cohomologyPullback_equiv₀]
  rfl

section Diagram

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (X.obj i).unop)]
  (F : DiagramCoefficientSystem X)

/-- Original stage cohomology and sections agree after lifting to a common universe,
with the actual compatible-system transition maps. -/
def diagramH0SectionsUliftIso :
    diagramCohomologyFunctor X F 0 ⋙ AddCommGrpCat.uliftFunctor.{u + 1, e} ≅
      diagramSectionsFunctor X F ⋙ AddCommGrpCat.uliftFunctor.{e, u + 1} :=
  NatIso.ofComponents (fun i =>
    (Sheaf.H.degreeZeroSectionsUliftIso (etaleTerminalIsTerminal (X.obj i).unop)).app
      (F.obj i)) (fun {_i _j} a =>
        cohomologyTransfer_zero_sectionsUlift (X.map a).unop
          (diagramInverseTransition X F a))

end Diagram

variable {I : Type u} [Category.{u} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (X.obj i).unop)]
  (c : Cocone X) [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]
  (F : DiagramCoefficientSystem X)

/-- The lifted original cohomology cocone is the actual section cocone transported
along the original degree-zero equivalence, including every cocone leg. -/
def diagramH0SectionsCoconeUliftIso :
    AddCommGrpCat.uliftFunctor.{u + 1, e}.mapCocone
        (diagramCohomologyCocone X c F 0) ≅
      (Cocone.precompose (diagramH0SectionsUliftIso X F).hom).obj
        (AddCommGrpCat.uliftFunctor.{e, u + 1}.mapCocone
          (compatibleSectionsCocone X F c)) := by
  refine Cocone.ext
    ((Sheaf.H.degreeZeroSectionsUliftIso (etaleTerminalIsTerminal c.pt.unop)).app
      (colimit (coneCoefficientFunctor X c F))) (fun i => ?_)
  change AddCommGrpCat.uliftFunctor.{u + 1, e}.map
      (diagramCohomologyLeg X c F 0 i) ≫
        ((Sheaf.H.degreeZeroSectionsUliftIso (etaleTerminalIsTerminal c.pt.unop)).app
          (colimit (coneCoefficientFunctor X c F))).hom =
    (diagramH0SectionsUliftIso X F).hom.app i ≫
      AddCommGrpCat.uliftFunctor.{e, u + 1}.map
        ((compatibleSectionsCocone X F c).ι.app i)
  rw [compatibleSectionsCocone_ι]
  exact cohomologyTransfer_zero_sectionsUlift (X := (X.obj i).unop) (Y := c.pt.unop)
    (c.ι.app i).unop (colimit.ι (coneCoefficientFunctor X c F) i)

/-- An actual section-colimit certificate supplies the original degree-zero
cohomology colimit. Only the section lift is used to preserve a colimit; the
cohomology lift is used solely to reflect it. The Ext universe remains independent. -/
def isColimitDiagramCohomologyZeroOfSections
    (hΓ : IsColimit (compatibleSectionsCocone X F c)) :
    IsColimit (diagramCohomologyCocone X c F 0) := by
  apply isColimitOfReflects AddCommGrpCat.uliftFunctor.{u + 1, e}
  exact IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (diagramH0SectionsUliftIso X F) _).symm
      (isColimitOfPreserves AddCommGrpCat.uliftFunctor.{e, u + 1} hΓ))
    (diagramH0SectionsCoconeUliftIso X c F).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
