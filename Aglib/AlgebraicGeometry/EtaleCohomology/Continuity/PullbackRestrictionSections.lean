/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackUnitTransport

/-! # Original restriction morphisms as relative sections -/
@[expose] public noncomputable section
open CategoryTheory Limits Opposite

private theorem inverse_of_comparison {C : Type*} [Category C]
    {A B D : C} (e : B ≅ D) (p : A ⟶ B) (r : A ⟶ D)
    (h : p ≫ e.hom = r) : r ≫ e.inv = p := by
  rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

/-- Original étale restriction followed by chart evaluation inverse is original pullback. -/
theorem etaleRestriction_evaluation_inv {S : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} S) (W : S.Etale)
    (g : W ⟶ etaleTerminal S) :
    F.obj.map g.op ≫ (pullbackSectionsEtaleEvaluationIso F W).inv =
      globalSectionsPullback W.hom F := by
  have hg : g = (etaleTerminalIsTerminal S).from W :=
    (etaleTerminalIsTerminal S).hom_ext _ _
  have h := globalSectionsPullback_etaleEvaluation F W
  exact inverse_of_comparison (pullbackSectionsEtaleEvaluationIso F W) _ _
    (h.trans (congrArg (fun q => F.obj.map q.op) hg).symm)

/-- The literal structural arrow uses the original inverse-image composition. -/
theorem structuralSectionsMap_eq {X S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) (W : S.Etale) :
    globalSectionsPullback W.hom ((inverseImage f).obj F) ≫
        (globalSections W.left).map ((inverseImageComp f W.hom).inv.app F) =
      pullbackSectionsMap F
        (Over.homMk W.hom (U := Over.mk (W.hom ≫ f)) (V := Over.mk f)) := by
  change _ = globalSectionsPullback W.hom ((inverseImage f).obj F) ≫
    (globalSections W.left).map ((pullbackTriangleIso (W.hom ≫ f) f W.hom rfl).inv.app F)
  simp only [pullbackTriangleIso, eqToIso_refl, Iso.trans_inv,
    Iso.refl_inv, Category.comp_id]

/-- Exact restriction morphism normalization for the original pullback coefficient. -/
theorem pullbackRestriction_evaluation_inv {X S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) (W : S.Etale)
    (g : W ⟶ etaleTerminal S) :
    ((inverseImage f).obj F).obj.map g.op ≫
        (pullbackSectionsEtaleEvaluationIso ((inverseImage f).obj F) W).inv ≫
        (globalSections W.left).map ((inverseImageComp f W.hom).inv.app F) =
      pullbackSectionsMap F
        (Over.homMk W.hom (U := Over.mk (W.hom ≫ f)) (V := Over.mk f)) := by
  have h := congrArg (fun q => q ≫
    (globalSections W.left).map ((inverseImageComp f W.hom).inv.app F))
    (etaleRestriction_evaluation_inv ((inverseImage f).obj F) W g)
  exact (Category.assoc _ _ _).symm.trans (h.trans (structuralSectionsMap_eq f F W))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
