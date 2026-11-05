/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ModuleRightTailUnderlyingCocone
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestRightTailColimit

/-! # Original native module right-tail section colimits

The complete original module cocone is compared after scalar forgetting with
the original abelian right-tail cocone. Existing geometric degree-zero
continuity supplies that abelian colimit; scalar forgetting reflects the
actual native module section colimit. No coefficient finiteness is needed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule

universe u r uI vI

variable (R : Type r) [Ring R]

attribute [local instance] ModuleCat.Sheaf.hasSheafify hasSheafifyLarge

section Comparison

variable {I : Type uI} [Category.{vI} I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (F : DiagramCoefficientSystem R X)
    [HasColimit (coneCoefficientFunctor R X c F)]
    [HasColimit (Continuity.coneCoefficientFunctor X c (underlyingSystem R X F))]
    [PreservesColimit (coneCoefficientFunctor R X c F) (underlying R c.pt.unop)]

/-- Evaluating the whole original cocone comparison retains every original
section leg and the unchanged additive-forgetting functor. -/
def rightTailSectionsUnderlyingCoconeIso (i : I) (T : (X.obj i).unop.Etale) :
    (Cocone.precompose (rightTailSectionsUnderlyingIso R X F i T).hom).obj
        (((sheafSections (X.obj i).unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (op T)).mapCocone (Continuity.diagramRightTailCocone X
            (underlyingSystem R X F) c i)) ≅
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).mapCocone
        (((sheafSections (X.obj i).unop.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
          (op T)).mapCocone (diagramRightTailCocone R X c F i)) := by
  refine Cocone.ext
    (((sheafSections (X.obj i).unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op T)).mapIso ((EtaleCohomology.directImage (c.ι.app i).unop).mapIso
        (coefficientColimitUnderlyingIso R X c F))) (fun a => ?_)
  change (𝟙 _) ≫
      ((Continuity.diagramRightTailCocone X (underlyingSystem R X F) c i).ι.app a).hom.app
        (op T) ≫
      ((EtaleCohomology.directImage (c.ι.app i).unop).map
        (coefficientColimitUnderlyingIso R X c F).hom).hom.app (op T) =
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
      (((diagramRightTailCocone R X c F i).ι.app a).hom.app (op T))
  rw [Category.id_comp]
  exact congrArg (fun q => q.hom.app (op T))
    (rightTailLeg_underlying R X c F i a)

end Comparison

section Continuity

variable {I : Type u} [Category.{u} I] [IsFiltered I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (hc : IsColimit c)
    [∀ {j k} (m : j ⟶ k), IsAffineHom (X.map m).unop]
    (F : DiagramCoefficientSystem R X)
    [HasColimit (coneCoefficientFunctor R X c F)]
    (i : I) (T : (X.obj i).unop.Etale)
    [CompactSpace T.left] [QuasiSeparatedSpace T.left]

/-- The literal native module right-tail cocone is colimiting after evaluation
on any original qcqs stage test, over an arbitrary fixed coefficient ring. -/
def isColimitDiagramRightTailEvaluation :
    IsColimit (((sheafSections (X.obj i).unop.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
      (op T)).mapCocone (diagramRightTailCocone R X c F i)) := by
  let : PreservesColimitsOfSize.{u + 1, u + 1} (underlying R c.pt.unop) :=
    ModuleCat.Sheaf.underlying_preservesColimits R c.pt.unop.smallEtaleTopology
  let : PreservesColimitsOfSize.{u, u} (underlying R c.pt.unop) :=
    preservesColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} (underlying R c.pt.unop)
  let : HasColimit (Continuity.coneCoefficientFunctor X c (underlyingSystem R X F)) :=
    hasColimit_of_iso (coneCoefficientUnderlyingIso R X c F)
  let EA := (sheafSections (X.obj i).unop.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op T)
  let hA := Continuity.isColimitDiagramRightTailEvaluation X c hc i T
    (underlyingSystem R X F)
  let hpre := (IsColimit.precomposeHomEquiv (rightTailSectionsUnderlyingIso R X F i T)
    (EA.mapCocone (Continuity.diagramRightTailCocone X
      (underlyingSystem R X F) c i))).symm hA
  apply isColimitOfReflects (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
  exact IsColimit.ofIsoColimit hpre (rightTailSectionsUnderlyingCoconeIso R X c F i T)

end Continuity

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
