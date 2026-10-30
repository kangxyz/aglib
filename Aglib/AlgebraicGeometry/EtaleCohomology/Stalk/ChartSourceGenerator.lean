/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartSourceSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PullbackEtaleEvaluation
public import Aglib.CategoryTheory.Sites.ConstantRestriction.TerminalValues

/-! # The original identity generator of the chart comparison source -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe v

private theorem cancel_inverse_sections {C D : Type*} [Category* C] [Category* D]
    (G : C ⥤ D) {A B : C} (e : A ≅ B) {Z H : D}
    (p : Z ⟶ G.obj B) (s : G.obj B ⟶ H) :
    (p ≫ G.map e.inv) ≫ (G.map e.hom ≫ s) = p ≫ s := by
  rw [Category.assoc, ← Category.assoc (G.map e.inv), ← G.map_comp,
    e.inv_hom_id, G.map_id, Category.id_comp]

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (U : X.Etale)

/-- The chart's terminal test object corresponds to the original terminal slice object. -/
def etaleSliceTerminalIso :
    (etaleSliceBackward U).obj (etaleTerminal U.left) ≅ Over.mk (𝟙 U) :=
  Over.isoMk (Continuity.siteEtalePostcomposeTerminalIso U) (by
    apply MorphismProperty.Over.Hom.ext
    change 𝟙 U.left ≫ 𝟙 U.left = 𝟙 U.left
    exact Category.id_comp _)

/-- The actual chart source, evaluated on the chart, equals the original slice source.
Both sides are homomorphisms from the original lifted integer object. -/
theorem chartComparisonSource_sections :
    (constantSheafAdj (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{u + 1}
      (etaleTerminalIsTerminal U.left)).homEquiv _ _ (chartComparisonSource U) ≫
        (Continuity.pullbackSectionsEtaleEvaluationIso
          (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
            (Scheme.smallEtaleTopology X) U) U).hom =
    (constantSheafAdj ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1}
      Over.mkIdTerminal).homEquiv _ _
      (Sheaf.SliceCohomology.sliceComparisonUnit.{u + 1, u, u + 1}
        (Scheme.smallEtaleTopology X) U) := by
  let F := Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
    (Scheme.smallEtaleTopology X) U
  let a := Sheaf.SliceCohomology.sliceComparisonUnit.{u + 1, u, u + 1}
    (Scheme.smallEtaleTopology X) U
  let b := chartSliceSource U ≫ (etaleSliceSheafEquivalence U).inverse.map a
  let adj := constantSheafAdj (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{u + 1}
    (etaleTerminalIsTerminal U.left)
  let e := (inverseImageEtaleIso U.hom).app F
  have hn := adj.homEquiv_naturality_right b e.inv
  have hc := cancel_inverse_sections (globalSections U.left) e
    (adj.homEquiv _ _ b) (F.obj.map (Continuity.siteEtalePostcomposeTerminalIso U).inv.op)
  change adj.homEquiv _ _ (b ≫ e.inv) ≫
    ((globalSections U.left).map e.hom ≫
      F.obj.map (Continuity.siteEtalePostcomposeTerminalIso U).inv.op) = _
  refine (congrArg (fun k => k ≫
    ((globalSections U.left).map e.hom ≫
      F.obj.map (Continuity.siteEtalePostcomposeTerminalIso U).inv.op)) hn).trans
    (hc.trans ?_)
  change (adj.homEquiv _ _
    (chartSliceSource U ≫ (etaleSliceSheafEquivalence U).inverse.map a)) ≫ _ = _
  rw [chartSliceSource_sections U (F.over U) a]
  exact Sheaf.ConstantTerminalValues.homEquiv_restrict ((Scheme.smallEtaleTopology X).over U)
    ((etaleTerminalIsTerminal U.left).isTerminalObj (etaleSliceBackward U))
    Over.mkIdTerminal (etaleSliceTerminalIso U).inv _ (F.over U) a

private theorem constantIntegerSections_apply {Y : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} Y)
    (a : (constantSheaf (Scheme.smallEtaleTopology Y) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ F) :
    (constantIntegerHomGlobalSectionsIso Y).hom.app F a =
      ((constantSheafAdj (Scheme.smallEtaleTopology Y) AddCommGrpCat.{u + 1}
        (etaleTerminalIsTerminal Y)).homEquiv _ F a) (ULift.up (1 : ℤ)) := rfl

/-- The original represented identity class is the generator of the chart source. -/
theorem chartComparisonSource_generator :
    (Continuity.pullbackSectionsEtaleEvaluationIso
      (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
        (Scheme.smallEtaleTopology X) U) U).hom
      ((constantIntegerHomGlobalSectionsIso U.left).hom.app _ (chartComparisonSource U)) =
    Sheaf.Hypercohomology.sectionsAddEquiv (Scheme.smallEtaleTopology X) U _ (𝟙 _) := by
  rw [constantIntegerSections_apply]
  have h := congrArg
    (fun k : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶
      (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
        (Scheme.smallEtaleTopology X) U).obj.obj (op U) => k (ULift.up (1 : ℤ)))
    (chartComparisonSource_sections U)
  exact h.trans (Sheaf.SliceCohomology.sliceComparisonUnit_generator.{u + 1, u, u + 1}
    (Scheme.smallEtaleTopology X) U)

end AlgebraicGeometry.Scheme.EtaleCohomology
