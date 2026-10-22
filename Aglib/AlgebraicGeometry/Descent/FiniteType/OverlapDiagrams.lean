/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FiniteType.RelativeOverlap
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Relative overlap diagrams over a fixed base

The source diagram varies over a fixed base. The chart and overlap systems
are native `opensDiagram` systems indexed by `Over i`; the product system
and its overlap arrow use the actual relative product maps. Their transition
squares are not asserted to be cartesian.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.RelativeOverlap

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
  {S : Scheme.{u}} (t : D ⟶ (Functor.const I).obj S)
  (i : I) (U V : (D.obj i).Opens)

/-- The structural map of a restricted chart system to the fixed base. -/
def chartStructure : opensDiagram D i U ⟶ (Functor.const (Over i)).obj S :=
  opensDiagramι D i U ≫ Functor.whiskerLeft (Over.forget i) t

@[simp]
lemma chartStructure_app (j : Over i) :
    (chartStructure D t i U).app j = (D.map j.hom ⁻¹ᵁ U).ι ≫ t.app j.left := rfl

/-- Inclusion of the literal inverse-image open systems. -/
def chartInclusion {U V : (D.obj i).Opens} (h : U ≤ V) :
    opensDiagram D i U ⟶ opensDiagram D i V where
  app j := (D.obj j.left).homOfLE (fun _ hx ↦ h hx)
  naturality j k q := by
    apply (cancel_mono (D.map k.hom ⁻¹ᵁ V).ι).mp
    simp [opensDiagram, Scheme.Hom.resLE_comp_ι]

/-- Products of two fixed-stage chart inverse images over the fixed base. -/
def productDiagram : Over i ⥤ Scheme.{u} where
  obj j := pullback ((chartStructure D t i U).app j) ((chartStructure D t i V).app j)
  map {j k} q := pullback.map _ _ _ _
    ((opensDiagram D i U).map q) ((opensDiagram D i V).map q) (𝟙 S)
    ((chartStructure D t i U).naturality q).symm
    ((chartStructure D t i V).naturality q).symm
  map_id j := by
    apply pullback.hom_ext <;> simp
  map_comp q r := by
    apply pullback.hom_ext <;> simp [Functor.map_comp, Category.assoc, Scheme.Hom.resLE_comp_resLE]

@[reassoc (attr := simp)]
lemma productDiagram_map_fst {j k : Over i} (q : j ⟶ k) :
    (productDiagram D t i U V).map q ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (opensDiagram D i U).map q :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma productDiagram_map_snd {j k : Over i} (q : j ⟶ k) :
    (productDiagram D t i U V).map q ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (opensDiagram D i V).map q :=
  pullback.lift_snd _ _ _

/-- The actual overlap arrows form a natural transformation. -/
def overlapMap : opensDiagram D i (U ⊓ V) ⟶ productDiagram D t i U V where
  app j := toProduct (t.app j.left) (D.map j.hom ⁻¹ᵁ U) (D.map j.hom ⁻¹ᵁ V)
  naturality j k q := by
    apply pullback.hom_ext
    · simp only [Category.assoc, productDiagram_map_fst]
      simpa only [chartStructure_app, chartInclusion, toProduct_fst,
        toProduct_fst_assoc] using (chartInclusion D i (U := U ⊓ V) (V := U)
          inf_le_left).naturality q
    · simp only [Category.assoc, productDiagram_map_snd]
      simpa only [chartStructure_app, chartInclusion, toProduct_snd,
        toProduct_snd_assoc] using (chartInclusion D i (U := U ⊓ V) (V := V)
          inf_le_right).naturality q

/-- The overlap family is locally of finite type at every stage, even when
the varying structural maps are not locally of finite type. -/
lemma locallyOfFiniteType_overlapMap_app (j : Over i) :
    LocallyOfFiniteType ((overlapMap D t i U V).app j) :=
  locallyOfFiniteType_toProduct _ _ _

end AlgebraicGeometry.Scheme.RelativeOverlap
