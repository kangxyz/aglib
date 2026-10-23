/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SchemeLimitHigher
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramH0Sections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestRightTailColimit

/-! # Original étale cohomology on qcqs inverse scheme limits

Actual qcqs section continuity supplies both degree-zero inputs of the original
higher-continuity induction. The comparison is the original pullback followed
by the coefficient-colimit insertion, in every degree. The Ext universe remains
independent of the scheme and index universe.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u e

attribute [local instance] hasSheafifyLarge

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (hc : IsColimit c)
  [∀ i, CompactSpace (X.obj i).unop] [∀ i, QuasiSeparatedSpace (X.obj i).unop]
  [∀ {i j} (a : i ⟶ j), IsAffineHom (X.map a).unop]
  [∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (X.obj i).unop)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.unop)]

/-- Genuine qcqs section continuity gives the original degree-zero cohomology cocone. -/
def isColimitDiagramCohomologyZeroOfQcqsStages (F : DiagramCoefficientSystem X) :
    IsColimit (diagramCohomologyCocone X c F 0) :=
  isColimitDiagramCohomologyZeroOfSections X c F
    (isColimitCompatibleSectionsOfQcqsStages X c hc F)

variable [HasColimitsOfShape I AddCommGrpCat.{e}]

include hc in
/-- The original cohomology comparison is invertible in every degree for an
actual qcqs inverse scheme limit with affine transitions and a compatible system.
No section-colimit or cohomology-comparison certificate is assumed. -/
theorem isIso_schemeLimitCohomologyComparison (n : ℕ) (F : DiagramCoefficientSystem X) :
    IsIso (schemeLimitCohomologyComparison X c F n) := by
  apply isIso_schemeLimitCohomologyComparison_of_sectionCocones X c hc
    (fun G ↦ isColimitDiagramCohomologyZeroOfQcqsStages X c hc G) ?_ n F
  intro Q _ i T hT
  have : CompactSpace T.left := hT.1
  have : QuasiSeparatedSpace T.left := hT.2
  exact isColimitDiagramRightTailEvaluation X c hc i T Q

/-- The actual original cohomology cocone is colimiting in every degree. -/
def isColimitDiagramCohomologyOfQcqsStages (F : DiagramCoefficientSystem X) (n : ℕ) :
    IsColimit (diagramCohomologyCocone X c F n) := by
  have : IsIso ((colimit.isColimit (diagramCohomologyFunctor X F n)).desc
      (diagramCohomologyCocone X c F n)) :=
    isIso_schemeLimitCohomologyComparison X c hc n F
  exact (colimit.isColimit (diagramCohomologyFunctor X F n)).ofPointIso

/-- The canonical all-degree continuity isomorphism has the original comparison as its hom. -/
def schemeLimitCohomologyIso (F : DiagramCoefficientSystem X) (n : ℕ) :
    colimit (diagramCohomologyFunctor X F n) ≅
      AddCommGrpCat.of (Sheaf.H.{e} (colimit (coneCoefficientFunctor X c F)) n) := by
  have := isIso_schemeLimitCohomologyComparison X c hc n F
  exact asIso (schemeLimitCohomologyComparison X c F n)

@[simp]
lemma schemeLimitCohomologyIso_hom (F : DiagramCoefficientSystem X) (n : ℕ) :
    (schemeLimitCohomologyIso X c hc F n).hom =
      schemeLimitCohomologyComparison X c F n := rfl

@[reassoc]
lemma ι_schemeLimitCohomologyIso_hom (F : DiagramCoefficientSystem X) (n : ℕ) (i : I) :
    colimit.ι (diagramCohomologyFunctor X F n) i ≫
        (schemeLimitCohomologyIso X c hc F n).hom = diagramCohomologyLeg X c F n i :=
  ι_schemeLimitCohomologyComparison X c F n i

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
