/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.RestrictionSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleTerminalSite
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageMate

/-! # Original ordinary exchange and literal chart evaluation

The original étale exchange, followed by the original terminal and chart
comparisons, is the original evaluation map. This is an equality of actual
ordinary maps, to be used termwise on genuine resolutions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

private theorem map_op_triangle {C D : Type*} [Category* C] [Category* D]
    (F : Cᵒᵖ ⥤ D) {A B C₀ D₀ : C} (p : A ⟶ B) (q : B ⟶ C₀)
    (r : C₀ ⟶ D₀) (s : A ⟶ D₀) (h : p ≫ q ≫ r = s) :
    F.map r.op ≫ F.map q.op ≫ F.map p.op = F.map s.op := by
  calc
    _ = F.map (p ≫ q ≫ r).op := by
      simp only [op_comp, F.map_comp, Category.assoc]
    _ = _ := congrArg (fun k => F.map k.op) h

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

private theorem etaleRestriction_terminal_path {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Etale) (F : AbelianSheaf.{u, u + 1} X) :
    (globalSections U.left).map ((etaleDirectImageRestrictionIso f U.hom).hom.app F) ≫
        (directImageGlobalSectionsIso (pullback.fst U.hom f)).hom.app
          ((etaleRestriction (pullback.snd U.hom f)).obj F) ≫
        F.obj.map
          (Continuity.siteEtalePostcomposeTerminalIso ((siteBaseChange f).obj U)).inv.op =
      F.obj.map ((siteBaseChange f).map
        (Continuity.siteEtalePostcomposeTerminalIso U).inv).op := by
  exact map_op_triangle F.obj
    (Continuity.siteEtalePostcomposeTerminalIso ((siteBaseChange f).obj U)).inv
    ((siteEtalePostcompose (pullback.snd U.hom f)).map
      (siteBaseChangeTerminalIso (pullback.fst U.hom f)).inv)
    ((siteEtaleDirectImageRestrictionIso f U.hom).hom.app (etaleTerminal U.left))
    ((siteBaseChange f).map (Continuity.siteEtalePostcomposeTerminalIso U).inv)
    (siteEtaleDirectImageRestriction_terminal f U)

/-- Literal chart evaluation is compatible with the SAME original ordinary
exchange, not merely with an isomorphic endpoint map. -/
theorem baseChangeMap_etaleEvaluation {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Etale) (F : AbelianSheaf.{u, u + 1} X) :
    (globalSections U.left).map
        ((baseChangeMap f (pullback.fst U.hom f) U.hom (pullback.snd U.hom f)
          pullback.condition).app F) ≫
        (directImageGlobalSectionsIso (pullback.fst U.hom f)).hom.app
          ((inverseImage (pullback.snd U.hom f)).obj F) ≫
        (Continuity.pullbackSectionsEtaleEvaluationIso F ((siteBaseChange f).obj U)).hom =
      (Continuity.pullbackSectionsEtaleEvaluationIso ((directImage f).obj F) U).hom := by
  exact exchange_sections_of_restriction_factorization
    (directImage f) (directImage (pullback.fst U.hom f))
    (inverseImage U.hom) (etaleRestriction U.hom)
    (inverseImage (pullback.snd U.hom f)) (etaleRestriction (pullback.snd U.hom f))
    (globalSections U.left) (globalSections (pullback U.hom f))
    (inverseImageEtaleIso U.hom) (inverseImageEtaleIso (pullback.snd U.hom f))
    (etaleDirectImageRestrictionIso f U.hom)
    (directImageGlobalSectionsIso (pullback.fst U.hom f))
    (baseChangeMap f (pullback.fst U.hom f) U.hom (pullback.snd U.hom f)
      pullback.condition) (etaleBaseChangeIso_hom f U.hom).symm F
    (F.obj.obj (op ((siteBaseChange f).obj U)))
    (F.obj.map
      (Continuity.siteEtalePostcomposeTerminalIso ((siteBaseChange f).obj U)).inv.op)
    (F.obj.map ((siteBaseChange f).map (Continuity.siteEtalePostcomposeTerminalIso U).inv).op)
    (Continuity.pullbackSectionsEtaleEvaluationIso F ((siteBaseChange f).obj U)).hom
    (Continuity.pullbackSectionsEtaleEvaluationIso ((directImage f).obj F) U).hom
    rfl rfl (etaleRestriction_terminal_path f U F)

end AlgebraicGeometry.Scheme.EtaleCohomology
