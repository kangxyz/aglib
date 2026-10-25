/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramEtaleTest
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSmallIndex

/-! # Evaluate the original limit coefficient diagram on the actual limit test chart -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X) (c : Cocone X) (i : I)
  (T : (X.obj i).unop.Etale)

/-- The outer functor evaluates the original cone coefficients, not a pulled-system colimit. -/
def diagramTestConeSectionsFunctor : Under i ⥤ AddCommGrpCat.{u + 1} :=
  Under.forget i ⋙ coneCoefficientFunctor X c F ⋙
    (sheafSections c.pt.unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (diagramEtaleTestLimitChart X i T c))

variable [HasColimit (coneCoefficientFunctor X c F)]

/-- The original coefficient insertion cocone, evaluated and restricted to the final tail. -/
def diagramTestConeSectionsCocone : Cocone (diagramTestConeSectionsFunctor X F c i T) :=
  (((sheafSections c.pt.unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (op (diagramEtaleTestLimitChart X i T c))).mapCocone
      (colimit.cocone (coneCoefficientFunctor X c F))).whisker (Under.forget i)

lemma diagramTestConeSectionsCocone_ι (a : Under i) :
    (diagramTestConeSectionsCocone X F c i T).ι.app a =
      (colimit.ι (coneCoefficientFunctor X c F) a.right).hom.app
        (op (diagramEtaleTestLimitChart X i T c)) := rfl

section Small
variable {J : Type u} [Category.{u} J] [IsFiltered J]
  (Y : J ⥤ Scheme.{u}ᵒᵖ) (G : DiagramCoefficientSystem Y) (d : Cocone Y)
  (j : J) (U : (Y.obj j).unop.Etale)
  [HasColimit (coneCoefficientFunctor Y d G)]
  [CompactSpace (diagramEtaleTestLimitChart Y j U d).left]
  [QuasiSeparatedSpace (diagramEtaleTestLimitChart Y j U d).left]

/-- The actual outer colimit uses fixed-site qcqs evaluation and native under-finality only. -/
def isColimitDiagramTestConeSections :
    IsColimit (diagramTestConeSectionsCocone Y G d j U) := by
  let := qcqsSectionsPreservesSmallFilteredColimits (diagramEtaleTestLimitChart Y j U d)
  exact (Functor.Final.isColimitWhiskerEquiv (Under.forget j) _).symm
    (isColimitOfPreserves
      ((sheafSections d.pt.unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (diagramEtaleTestLimitChart Y j U d)))
      (colimit.isColimit (coneCoefficientFunctor Y d G)))

end Small
end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
