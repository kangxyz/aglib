/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackUnitTransport

/-! # Original chart-unit sections through actual inverse-image composition

The original unit at a chart, restricted by its actual relative terminal test,
retains the original inverse-image composition map. This is the section input
for native horizontal pasting of the original higher exchange.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

private theorem section_iso_cancel {C : Type*} [Category* C]
    {A B P Q : C} (e : P ≅ Q) (r : A ⟶ B) (s : B ⟶ Q) (t : A ⟶ P)
    (h : r ≫ s ≫ e.inv = t) : t ≫ e.hom = r ≫ s := by
  rw [← h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

/-- The actual relative terminal-test unit, followed by original inverse-image
composition, is original chart evaluation followed by original section pullback. -/
theorem unitSectionMap_relativeTerminalTest_comp {S T : Scheme.{u}}
    (U : S.Etale) (b : T ⟶ U.left) (F : AbelianSheaf.{u, u + 1} S) :
    Continuity.unitSectionMap (b ≫ U.hom) F
        (Continuity.relativeTerminalTest (b ≫ U.hom) U b rfl) ≫
        (globalSections T).map ((inverseImageComp U.hom b).hom.app F) =
      (Continuity.pullbackSectionsEtaleEvaluationIso F U).inv ≫
        globalSectionsPullback b ((inverseImage U.hom).obj F) := by
  let e := (globalSections T).mapIso ((inverseImageComp U.hom b).app F)
  have ht : Continuity.pullbackSectionsMap F
      (Over.homMk b rfl : Over.mk (b ≫ U.hom) ⟶ Over.mk U.hom) =
      globalSectionsPullback b ((inverseImage U.hom).obj F) ≫ e.inv := by
    dsimp only [Continuity.pullbackSectionsMap]
    congr 1
  have h := Continuity.pullbackSectionsMap_relativeTerminalTest F (b ≫ U.hom) U b rfl
  rw [ht] at h
  exact section_iso_cancel e (Continuity.pullbackSectionsEtaleEvaluationIso F U).inv
    (globalSectionsPullback b ((inverseImage U.hom).obj F))
    (Continuity.unitSectionMap (b ≫ U.hom) F
      (Continuity.relativeTerminalTest (b ≫ U.hom) U b rfl)) h

end AlgebraicGeometry.Scheme.EtaleCohomology
