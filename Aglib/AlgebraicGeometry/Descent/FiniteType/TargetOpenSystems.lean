/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Actual varying-source systems restricted to a fixed target open

The source system is the native `opensDiagram` on `Over i`, using the
inverse image of a target open at stage `i`. Its structure maps and limit
map are literal `resLE` maps to the target open. Naturality identifies the
inverse-image opens and gives actual cartesian restriction squares.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.TargetOpenSystem

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
  {S : Scheme.{u}} (t : D ⟶ (Functor.const I).obj S)
  (i : I) (V : S.Opens)

/-- Naturality identifies the native fixed-stage inverse image with the
inverse image of the target open under the actual structural map. -/
lemma stageOpen_eq (j : Over i) :
    D.map j.hom ⁻¹ᵁ (t.app i ⁻¹ᵁ V) = t.app j.left ⁻¹ᵁ V := by
  change (D.map j.hom ≫ t.app i) ⁻¹ᵁ V = _
  have ht : D.map j.hom ≫ t.app i = t.app j.left := by
    exact (t.naturality j.hom).trans (Category.comp_id _)
  rw [ht]

/-- The actual structural map from a native chart stage to the target open. -/
def stageMap (j : Over i) : (opensDiagram D i (t.app i ⁻¹ᵁ V)).obj j ⟶ V.toScheme :=
  (t.app j.left).resLE V _ (stageOpen_eq D t i V j).le

@[reassoc (attr := simp)]
lemma stageMap_ι (j : Over i) : stageMap D t i V j ≫ V.ι =
    (D.map j.hom ⁻¹ᵁ (t.app i ⁻¹ᵁ V)).ι ≫ t.app j.left :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The actual restricted structure maps form a natural transformation. -/
def structureMap : opensDiagram D i (t.app i ⁻¹ᵁ V) ⟶ (Functor.const (Over i)).obj V.toScheme where
  app := stageMap D t i V
  naturality j k q := by
    have hw : (opensDiagram D i (t.app i ⁻¹ᵁ V)).map q ≫
        (D.map k.hom ⁻¹ᵁ (t.app i ⁻¹ᵁ V)).ι =
      (D.map j.hom ⁻¹ᵁ (t.app i ⁻¹ᵁ V)).ι ≫ D.map q.left :=
      (opensDiagramι D i (t.app i ⁻¹ᵁ V)).naturality q
    have ht : D.map q.left ≫ t.app k.left = t.app j.left :=
      (t.naturality q.left).trans (Category.comp_id _)
    apply (cancel_mono V.ι).mp
    change ((opensDiagram D i (t.app i ⁻¹ᵁ V)).map q ≫ stageMap D t i V k) ≫ V.ι =
      (stageMap D t i V j ≫ 𝟙 V.toScheme) ≫ V.ι
    calc
      _ = (opensDiagram D i (t.app i ⁻¹ᵁ V)).map q ≫
          ((D.map k.hom ⁻¹ᵁ (t.app i ⁻¹ᵁ V)).ι ≫ t.app k.left) := by
        rw [Category.assoc, stageMap_ι]
      _ = ((D.map j.hom ⁻¹ᵁ (t.app i ⁻¹ᵁ V)).ι ≫ D.map q.left) ≫ t.app k.left := by
        rw [← Category.assoc, hw]
      _ = (D.map j.hom ⁻¹ᵁ (t.app i ⁻¹ᵁ V)).ι ≫ t.app j.left := by
        rw [Category.assoc, ht]
      _ = _ := by rw [Category.comp_id, stageMap_ι]


/-- The stage map is the actual target-open pullback of the structural map. -/
lemma isPullback_stageMap (j : Over i) :
    IsPullback (stageMap D t i V j) (D.map j.hom ⁻¹ᵁ (t.app i ⁻¹ᵁ V)).ι
      V.ι (t.app j.left) := by
  apply IsOpenImmersion.isPullback
  · exact (stageMap_ι D t i V j).symm
  · simpa only [Scheme.Opens.opensRange_ι] using (stageOpen_eq D t i V j).symm

variable (c : Cone D) (h : c.pt ⟶ S) (hcompat : ∀ j, c.π.app j ≫ t.app j = h)

include hcompat in
lemma limitOpen_eq : c.π.app i ⁻¹ᵁ (t.app i ⁻¹ᵁ V) = h ⁻¹ᵁ V := by
  change (c.π.app i ≫ t.app i) ⁻¹ᵁ V = _
  rw [hcompat]

/-- The literal structural map from the native chart cone to the target open. -/
def limitMap : (opensCone D c i (t.app i ⁻¹ᵁ V)).pt ⟶ V.toScheme :=
  h.resLE V _ (limitOpen_eq D t i V c h hcompat).le

@[reassoc (attr := simp)]
lemma limitMap_ι : limitMap D t i V c h hcompat ≫ V.ι =
    (c.π.app i ⁻¹ᵁ (t.app i ⁻¹ᵁ V)).ι ≫ h := Scheme.Hom.resLE_comp_ι _ _

/-- The actual native chart-cone projection commutes with open inclusions. -/
lemma coneProjection_ι (j : Over i) :
    (opensCone D c i (t.app i ⁻¹ᵁ V)).π.app j ≫
        (D.map j.hom ⁻¹ᵁ (t.app i ⁻¹ᵁ V)).ι =
      (c.π.app i ⁻¹ᵁ (t.app i ⁻¹ᵁ V)).ι ≫ c.π.app j.left :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The literal restricted limit map commutes with the actual stage maps. -/
lemma cone_compatibility (j : Over i) :
    (opensCone D c i (t.app i ⁻¹ᵁ V)).π.app j ≫ (structureMap D t i V).app j =
      limitMap D t i V c h hcompat := by
  apply (cancel_mono V.ι).mp
  change (opensCone D c i (t.app i ⁻¹ᵁ V)).π.app j ≫ stageMap D t i V j ≫ V.ι = _
  rw [stageMap_ι, limitMap_ι, ← Category.assoc, coneProjection_ι, Category.assoc, hcompat]

/-- The cone map is the actual target-open pullback of the limit map. -/
lemma isPullback_limitMap :
    IsPullback (limitMap D t i V c h hcompat) (c.π.app i ⁻¹ᵁ (t.app i ⁻¹ᵁ V)).ι V.ι h := by
  apply IsOpenImmersion.isPullback
  · exact (limitMap_ι D t i V c h hcompat).symm
  · simpa only [Scheme.Opens.opensRange_ι] using (limitOpen_eq D t i V c h hcompat).symm

end AlgebraicGeometry.Scheme.TargetOpenSystem
