/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartSourceGenerator
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackEtaleNaturality

/-! # Original constant-source Hom on étale charts -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (U : X.Etale)

/-- Actual constant-source Hom, global sections, and chart evaluation. -/
def chartHomSectionsEquiv (F : AbelianSheaf.{u, u + 1} X) :
    (((constantSheaf (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ (inverseImage U.hom).obj F) ≃+
        F.obj.obj (op U) :=
  (((constantIntegerHomGlobalSectionsIso U.left).app ((inverseImage U.hom).obj F)) ≪≫
    Continuity.pullbackSectionsEtaleEvaluationIso F U).addCommGroupIsoToAddEquiv

/-- Coefficient naturality uses the original inverse-image map. -/
theorem chartHomSectionsEquiv_naturality {F G : AbelianSheaf.{u, u + 1} X}
    (q : F ⟶ G)
    (a : ((constantSheaf (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ (inverseImage U.hom).obj F) :
    chartHomSectionsEquiv U G (a ≫ (inverseImage U.hom).map q) =
      q.hom.app (op U) (chartHomSectionsEquiv U F a) := by
  have hc := ConcreteCategory.congr_hom
    ((constantIntegerHomGlobalSectionsIso U.left).hom.naturality
      ((inverseImage U.hom).map q)) a
  have he := ConcreteCategory.congr_hom
    (Continuity.pullbackSectionsEtaleEvaluationIso_naturality q U)
    ((constantIntegerHomGlobalSectionsIso U.left).hom.app _ a)
  exact (congrArg (Continuity.pullbackSectionsEtaleEvaluationIso G U).hom hc).trans he

/-- The native constant transport and triangle transport induce original restriction. -/
theorem chartHomSectionsEquiv_restriction {U V : X.Etale} (g : V ⟶ U)
    (F : AbelianSheaf.{u, u + 1} X)
    (a : ((constantSheaf (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ (inverseImage U.hom).obj F) :
    chartHomSectionsEquiv V F
      ((((inverseImageConstantIso g.left).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫
        (inverseImage g.left).map a) ≫
          (pullbackTriangleIso V.hom U.hom g.left
            (MorphismProperty.Over.w g)).inv.app F) =
      F.obj.map g.op (chartHomSectionsEquiv U F a) := by
  let c := ((inverseImageConstantIso g.left).app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv
  let k := (pullbackTriangleIso V.hom U.hom g.left
    (MorphismProperty.Over.w g)).inv.app F
  let b : (constantSheaf (Scheme.smallEtaleTopology V.left) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
        (inverseImage g.left).obj ((inverseImage U.hom).obj F) :=
    c ≫ (inverseImage g.left).map a
  have hc := ConcreteCategory.congr_hom (C := AddCommGrpCat.{u + 1})
    ((constantIntegerHomGlobalSectionsIso V.left).hom.naturality k) b
  have hp := constantIntegerHomGlobalSectionsIso_pullback g.left a
  have he := ConcreteCategory.congr_hom (Continuity.pullbackSectionsMap_etaleEvaluation F g)
    ((constantIntegerHomGlobalSectionsIso U.left).hom.app _ a)
  have hc' : (constantIntegerHomGlobalSectionsIso V.left).hom.app _ (b ≫ k) =
      (globalSections V.left).map k
        ((constantIntegerHomGlobalSectionsIso V.left).hom.app _ b) := hc
  exact (congrArg (Continuity.pullbackSectionsEtaleEvaluationIso F V).hom hc').trans
    ((congrArg (fun z => (Continuity.pullbackSectionsEtaleEvaluationIso F V).hom
      ((globalSections V.left).map k z)) hp).trans he)

/-- The represented identity is the actual source comparison under the Hom equivalence. -/
theorem chartHomSectionsEquiv_source :
    chartHomSectionsEquiv U
      (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
        (Scheme.smallEtaleTopology X) U) (chartComparisonSource U) =
      Sheaf.Hypercohomology.sectionsAddEquiv (Scheme.smallEtaleTopology X) U _ (𝟙 _) :=
  chartComparisonSource_generator U

end AlgebraicGeometry.Scheme.EtaleCohomology
