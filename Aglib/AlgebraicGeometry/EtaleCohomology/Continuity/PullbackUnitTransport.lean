/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackUnitGeometry

/-! # Original local representatives as relative global sections -/
@[expose] public noncomputable section
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

/-- Original relative section transport into an étale chart equals the original unit
on the corresponding terminal test object. -/
theorem pullbackSectionsMap_relativeTerminalTest {X S : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (f : S ⟶ X) (U : X.Etale)
    (b : S ⟶ U.left) (h : b ≫ U.hom = f) :
    (pullbackSectionsEtaleEvaluationIso F U).inv ≫
        pullbackSectionsMap F (Over.homMk b h : Over.mk f ⟶ Over.mk U.hom) =
      unitSectionMap f F (relativeTerminalTest f U b h) := by
  subst f
  have hu := unitSectionMap_comp U.hom b F (chartDiagonal U)
    (siteBaseChangeTerminalIso b).inv
  have he : (pullbackSectionsEtaleEvaluationIso F U).inv =
      unitSectionMap U.hom F (chartDiagonal U) := pullbackSectionsEtaleEvaluationIso_inv F U
  have hp : globalSectionsPullback b ((inverseImage U.hom).obj F) =
      unitSectionMap b ((inverseImage U.hom).obj F) (siteBaseChangeTerminalIso b).inv := rfl
  have ht : (globalSections S).map
      ((pullbackTriangleIso (b ≫ U.hom) U.hom b rfl).inv.app F) =
      ((inverseImageComp U.hom b).inv.app F).hom.app (op (etaleTerminal S)) := by
    simp only [pullbackTriangleIso, eqToIso_refl, Iso.trans_inv,
      Iso.refl_inv, Category.comp_id]
    rfl
  change (pullbackSectionsEtaleEvaluationIso F U).inv ≫
    (globalSectionsPullback b ((inverseImage U.hom).obj F) ≫ _) = _
  exact (congrArg₂ (fun x y => x ≫ y) he
    (congrArg₂ (fun x y => x ≫ y) hp ht)).trans
      (hu.trans (congrArg (unitSectionMap (b ≫ U.hom) F)
        (composedTestMap_terminal U b)))

/-- An arbitrary original inverse-image unit representative becomes exactly the original
relative section transport after the native chart and coefficient identifications. -/
theorem unitSectionMap_etaleEvaluation {X S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) {U : X.Etale} {W : S.Etale}
    (a : W ⟶ (siteBaseChange f).obj U) :
    unitSectionMap f F a ≫
        (pullbackSectionsEtaleEvaluationIso ((inverseImage f).obj F) W).inv ≫
        (globalSections W.left).map ((inverseImageComp f W.hom).inv.app F) =
      (pullbackSectionsEtaleEvaluationIso F U).inv ≫
        pullbackSectionsMap F (unitRepresentativeArrow f a) := by
  have hu := unitSectionMap_comp f W.hom F a (chartDiagonal W)
  have he : (pullbackSectionsEtaleEvaluationIso ((inverseImage f).obj F) W).inv =
      unitSectionMap W.hom ((inverseImage f).obj F) (chartDiagonal W) :=
    pullbackSectionsEtaleEvaluationIso_inv ((inverseImage f).obj F) W
  have ht := pullbackSectionsMap_relativeTerminalTest F (W.hom ≫ f) U
    (unitRepresentativeArrow f a).left (Over.w (unitRepresentativeArrow f a))
  rw [he]
  exact (hu.trans (congrArg (unitSectionMap (W.hom ≫ f) F)
    (composedTestMap_diagonal f a))).trans ht.symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
