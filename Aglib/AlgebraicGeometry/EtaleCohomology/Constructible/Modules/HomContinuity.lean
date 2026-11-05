/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.HomCocones
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ModuleRightTailColimit

/-! # Actual fixed-ring Hom continuity for native source stages

Original varying module sections on affine tests provide the free-generator
Hom colimits. Native finite-colimit source closure then gives the unchanged
right-tail Hom cocone for every original finite stage over the same ring.
No constructibility or finiteness of an underlying additive carrier is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.NativeFreePresentation

universe u

attribute [local instance] ModuleCat.Sheaf.hasSheafify Cardinal.fact_isRegular_aleph0

open Continuity.NativeModule

/-- The original Hom cocone is colimiting for every native finite stage. -/
def isColimitHomRightTail (R : Type (u + 1)) [Ring R]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (hc : IsColimit c)
    [∀ {j k} (a : j ⟶ k), IsAffineHom (X.map a).unop]
    (F : Continuity.NativeModule.DiagramCoefficientSystem R X)
    [HasColimit (Continuity.NativeModule.coneCoefficientFunctor R X c F)]
    (i : I) (A : Continuity.NativeModule.Coefficient R (X.obj i).unop)
    (hA : finiteColimitStages R (X.obj i).unop A) :
    IsColimit ((coyoneda.obj (op A)).mapCocone
      (Continuity.NativeModule.diagramRightTailCocone R X c F i)) := by
  apply canonicalHomCoconeIsColimit R (X.obj i).unop
    (Continuity.NativeModule.diagramRightTailCocone R X c F i) ?_ A hA
  intro U
  let T := (Scheme.AffineEtale.Spec (X.obj i).unop).obj U
  have : IsAffine T.left := by
    change IsAffine (Spec U.left.unop)
    infer_instance
  let E := ModuleCat.Sheaf.freeRepresentableEvaluationIso.{u + 1, u + 1, u, 0}
    (X.obj i).unop.smallEtaleTopology R T
  have hsections := Continuity.NativeModule.isColimitDiagramRightTailEvaluation
    R X c hc F i T
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  have heval : IsColimit ((ModuleCat.Sheaf.evaluation.{u + 1, u + 1, u, 0}
      (X.obj i).unop.smallEtaleTopology R T).mapCocone
        (Continuity.NativeModule.diagramRightTailCocone R X c F i)) :=
    isColimitOfPreserves (CategoryTheory.forget (ModuleCat.{u + 1} R)) hsections
  exact IsColimit.mapCoconeEquiv E.symm heval

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.NativeFreePresentation
