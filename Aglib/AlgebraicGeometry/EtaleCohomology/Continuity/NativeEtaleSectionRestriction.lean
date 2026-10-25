/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackScalarTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackEtaleEvaluation

/-! # Original relative sections and original étale sheaf restriction -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

private theorem cancel_section_evaluation_factors {C : Type*} [Category C]
    {A B D E : C} (f : A ⟶ B) (e : D ≅ B) (g : B ⟶ E) :
    (f ≫ e.inv) ≫ (e.hom ≫ g) = f ≫ g := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u

attribute [local instance] hasSheafifyLarge

/-- The original triangle coefficient comparison and original étale evaluation
identify relative sections with the original inverse-image sheaf on the chart. -/
def nativeEtaleSectionEvaluationIso {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) {Y C : Over X} (R : Y ⟶ C) [Etale R.left] :
    (pullbackSectionsFunctor F).obj (op Y) ≅
      ((inverseImage C.hom).obj F).obj.obj (op (Scheme.Etale.mk R.left)) :=
  (globalSections Y.left).mapIso
      ((pullbackTriangleIso Y.hom C.hom R.left (Over.w R)).app F) ≪≫
    pullbackSectionsEtaleEvaluationIso ((inverseImage C.hom).obj F) (Scheme.Etale.mk R.left)

/-- The whole original relative section map is the original sheaf restriction,
after the actual chart evaluation comparison. Triangle cancellation takes place
before any section elements or covering family are introduced. -/
theorem nativeEtaleSectionEvaluation_restriction {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) {Y C : Over X} (R : Y ⟶ C) [Etale R.left] :
    (pullbackSectionsFunctor F).map R.op ≫ (nativeEtaleSectionEvaluationIso F R).hom =
      ((inverseImage C.hom).obj F).obj.map
        ((etaleTerminalIsTerminal C.left).from (Scheme.Etale.mk R.left)).op := by
  exact (cancel_section_evaluation_factors
    (globalSectionsPullback R.left ((inverseImage C.hom).obj F))
    ((globalSections Y.left).mapIso
      ((pullbackTriangleIso Y.hom C.hom R.left (Over.w R)).app F))
    (pullbackSectionsEtaleEvaluationIso ((inverseImage C.hom).obj F)
      (Scheme.Etale.mk R.left)).hom).trans
    (globalSectionsPullback_etaleEvaluation ((inverseImage C.hom).obj F)
      (Scheme.Etale.mk R.left))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
