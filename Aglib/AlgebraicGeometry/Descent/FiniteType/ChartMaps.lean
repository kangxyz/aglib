/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.BaseChangeMaps
public import Aglib.AlgebraicGeometry.Descent.FiniteType.AffineCharts
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Gluing

/-!
# Actual arrows between fixed-chart base-change systems

The source and target use the base-first pullback convention of
`Scheme.baseChangeDiagram`. Their arrows are compared explicitly with the
source-first convention of `Over.pullback`. Naturality and cartesian squares
are statements about the actual maps, not just about their source objects.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.BaseChangeChart

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ Scheme.{u}) (i : I)
  {A B : Over (D.obj i)} (a : A ⟶ B) (V : B.left.Opens)

/-- Pullback of the original restricted arrow, in the base-first convention. -/
def baseChangeMap {T : Scheme.{u}} (b : T ⟶ D.obj i) :
    pullback b (source D i a V).hom ⟶ pullback b (target D i V).hom :=
  baseChangeOverHom b (map D i a V)

@[reassoc (attr := simp)]
lemma baseChangeMap_fst {T : Scheme.{u}} (b : T ⟶ D.obj i) :
    baseChangeMap D i a V b ≫ pullback.fst b (target D i V).hom =
      pullback.fst b (source D i a V).hom := by
  exact baseChangeOverHom_fst b (map D i a V)

@[reassoc (attr := simp)]
lemma baseChangeMap_snd {T : Scheme.{u}} (b : T ⟶ D.obj i) :
    baseChangeMap D i a V b ≫ pullback.snd b (target D i V).hom =
      pullback.snd b (source D i a V).hom ≫ (map D i a V).left := by
  exact baseChangeOverHom_snd b (map D i a V)

/-- The exact comparison with the native over-category pullback arrow. -/
lemma baseChangeMap_eq_overPullback {T : Scheme.{u}} (b : T ⟶ D.obj i) :
    baseChangeMap D i a V b =
      (pullbackSymmetry b (source D i a V).hom).hom ≫
        ((Over.pullback b).map (map D i a V)).left ≫
          (pullbackSymmetry (target D i V).hom b).hom := by
  exact baseChangeOverHom_eq_overPullback b (map D i a V)

/-- The actual arrow is cartesian over the original restricted arrow. -/
lemma isPullback_baseChangeMap {T : Scheme.{u}} (b : T ⟶ D.obj i) :
    IsPullback (baseChangeMap D i a V b)
      (pullback.snd b (source D i a V).hom)
      (pullback.snd b (target D i V).hom) (map D i a V).left := by
  exact isPullback_baseChangeOverHom b (map D i a V)

/-- The literal arrow at one stage of the original `Over i` system. -/
abbrev stageMap (j : Over i) :
    (sourceDiagram D i a V).obj j ⟶ (targetDiagram D i V).obj j :=
  baseChangeMap D i a V (D.map j.hom)

/-- The literal arrow between the two canonical cone points. -/
abbrev limitMap (c : Cone D) :
    (sourceCone D i a V c).pt ⟶ (targetCone D i V c).pt :=
  baseChangeMap D i a V (c.π.app i)

/-- Stage arrows commute with the actual transition maps. -/
@[reassoc]
lemma stageMap_naturality {j k : Over i} (q : j ⟶ k) :
    stageMap D i a V j ≫ (targetDiagram D i V).map q =
      (sourceDiagram D i a V).map q ≫ stageMap D i a V k := by
  apply pullback.hom_ext <;>
    simp [stageMap, sourceDiagram, targetDiagram, Category.assoc]

/-- The canonical cone projections preserve the specified restricted arrow. -/
@[reassoc]
lemma limitMap_comp_π (c : Cone D) (j : Over i) :
    limitMap D i a V c ≫ (targetCone D i V c).π.app j =
      (sourceCone D i a V c).π.app j ≫ stageMap D i a V j := by
  apply pullback.hom_ext <;>
    simp [limitMap, stageMap, sourceCone, targetCone, Category.assoc]

/-- The stage arrows form a natural transformation of the original diagrams. -/
def diagramMap : sourceDiagram D i a V ⟶ targetDiagram D i V where
  app := stageMap D i a V
  naturality _ _ q := (stageMap_naturality D i a V q).symm

/-- Every transition square of the chart arrows is an actual pullback. -/
lemma isPullback_stageMap {j k : Over i} (q : j ⟶ k) :
    IsPullback (stageMap D i a V j) ((sourceDiagram D i a V).map q)
      ((targetDiagram D i V).map q) (stageMap D i a V k) := by
  apply IsPullback.of_bot (v₂₁ := pullback.snd (D.map k.hom) (source D i a V).hom)
    (v₂₂ := pullback.snd (D.map k.hom) (target D i V).hom)
    _ (stageMap_naturality D i a V q) (isPullback_baseChangeMap D i a V (D.map k.hom))
  simpa only [sourceDiagram, targetDiagram, baseChangeDiagram_map_snd] using
    (isPullback_baseChangeMap D i a V (D.map j.hom))

/-- Every cone square of the chart arrows is an actual pullback. -/
lemma isPullback_limitMap (c : Cone D) (j : Over i) :
    IsPullback (limitMap D i a V c) ((sourceCone D i a V c).π.app j)
      ((targetCone D i V c).π.app j) (stageMap D i a V j) := by
  apply IsPullback.of_bot (v₂₁ := pullback.snd (D.map j.hom) (source D i a V).hom)
    (v₂₂ := pullback.snd (D.map j.hom) (target D i V).hom)
    _ (limitMap_comp_π D i a V c j) (isPullback_baseChangeMap D i a V (D.map j.hom))
  simpa only [sourceCone, targetCone, baseChangeCone_π_app_snd] using
    (isPullback_baseChangeMap D i a V (c.π.app i))

end AlgebraicGeometry.Scheme.BaseChangeChart
