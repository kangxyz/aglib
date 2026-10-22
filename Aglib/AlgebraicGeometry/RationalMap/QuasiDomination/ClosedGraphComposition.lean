/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Composing a closed graph with a closed relative target

A genuine base change of the closed target inclusion, followed by canonical
pullback associativity isomorphisms, sends the intermediate graph to its
literal graph over the original base. No density assumption is involved.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

variable {B X Y Z C D : Scheme.{u}}
    (β : B ⟶ X) (f : Y ⟶ X) (i : Z ⟶ pullback β f) (α : C ⟶ B)

/-- The canonical map from the product with the closed target to the original
relative product, using actual base change and pullback associativity. -/
def closedGraphCompositionMap :
    pullback α (i ≫ pullback.fst β f) ⟶ pullback (α ≫ β) f :=
  (pullbackLeftPullbackSndIso α (pullback.fst β f) i).inv ≫
    pullback.fst (pullback.snd α (pullback.fst β f)) i ≫
      (pullbackRightPullbackFstIso β f α).hom

@[reassoc (attr := simp)]
lemma closedGraphCompositionMap_fst :
    closedGraphCompositionMap β f i α ≫ pullback.fst (α ≫ β) f =
      pullback.fst α (i ≫ pullback.fst β f) := by
  simp [closedGraphCompositionMap, Category.assoc]

@[reassoc (attr := simp)]
lemma closedGraphCompositionMap_snd :
    closedGraphCompositionMap β f i α ≫ pullback.snd (α ≫ β) f =
      pullback.snd α (i ≫ pullback.fst β f) ≫ i ≫ pullback.snd β f := by
  simp [closedGraphCompositionMap, Category.assoc]

instance [IsClosedImmersion i] : IsClosedImmersion (closedGraphCompositionMap β f i α) := by
  unfold closedGraphCompositionMap
  infer_instance

/-- The original structural triangle determines the final graph triangle. -/
lemma graph_comp_closedTarget_over (d : D ⟶ C) (h : D ⟶ Z)
    (w : d ≫ α = h ≫ (i ≫ pullback.fst β f)) :
    d ≫ (α ≫ β) = (h ≫ i ≫ pullback.snd β f) ≫ f := by
  calc
    d ≫ (α ≫ β) = (d ≫ α) ≫ β := (Category.assoc _ _ _).symm
    _ = h ≫ i ≫ pullback.fst β f ≫ β := by rw [w]; simp only [Category.assoc]
    _ = (h ≫ i ≫ pullback.snd β f) ≫ f := by
      rw [pullback.condition]
      simp only [Category.assoc]

/-- Closedness of the intermediate literal graph and the target inclusion
implies closedness of the final literal graph over the original base. The
last equality may be any proof of the triangle established above. -/
theorem isClosedImmersion_graph_comp_closedTarget [IsClosedImmersion i]
    (d : D ⟶ C) (h : D ⟶ Z)
    (w : d ≫ α = h ≫ (i ≫ pullback.fst β f))
    (hw : d ≫ (α ≫ β) = (h ≫ i ≫ pullback.snd β f) ≫ f)
    [IsClosedImmersion (pullback.lift d h w)] :
    IsClosedImmersion (pullback.lift d (h ≫ i ≫ pullback.snd β f) hw) := by
  have hgraph : pullback.lift d (h ≫ i ≫ pullback.snd β f) hw =
      pullback.lift d h w ≫ closedGraphCompositionMap β f i α := by
    apply pullback.hom_ext <;> simp only [Category.assoc,
      closedGraphCompositionMap_fst, closedGraphCompositionMap_snd,
      pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc]
  rw [hgraph]
  infer_instance

end AlgebraicGeometry.Scheme.QuasiDomination
