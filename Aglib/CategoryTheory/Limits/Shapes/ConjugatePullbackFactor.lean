/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Actual factors through conjugate pullbacks

A map into a conjugate of a cover gives a map from the corresponding changed
base to the original selected pullback. The map is constructed from the native
pullback universal property; both original projections are retained. The
construction is categorical and has no connectedness or vanishing assumptions.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

section BaseMaps

variable {X S T U : C} (p : X ⟶ S) (r : T ⟶ S) (s : U ⟶ S)
    (t : U ⟶ T) (ht : t ≫ r = s)

/-- Change only the original base coordinate of a native pullback. -/
def pullback.baseMap : pullback p s ⟶ pullback p r :=
  pullback.lift (pullback.fst p s) (pullback.snd p s ≫ t) (by
    rw [Category.assoc, ht]
    exact pullback.condition)

@[reassoc (attr := simp)]
theorem pullback.baseMap_fst :
    pullback.baseMap p r s t ht ≫ pullback.fst p r = pullback.fst p s :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullback.baseMap_snd :
    pullback.baseMap p r s t ht ≫ pullback.snd p r = pullback.snd p s ≫ t :=
  pullback.lift_snd _ _ _

/-- Composition of the actual base-coordinate maps. -/
theorem pullback.baseMap_comp {V : C} (v : V ⟶ S) (w : V ⟶ U)
    (hw : w ≫ s = v) :
    pullback.baseMap p s v w hw ≫ pullback.baseMap p r s t ht =
      pullback.baseMap p r v (w ≫ t) (by rw [Category.assoc, ht, hw]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.baseMap_fst]
  · simp only [Category.assoc, pullback.baseMap_snd, pullback.baseMap_snd_assoc]

/-- The actual pullback of an original section. -/
def pullback.sectionMap (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S) :
    T ⟶ pullback p r :=
  pullback.lift (r ≫ σ) (𝟙 T) (by rw [Category.assoc, hσ]; simp)

@[reassoc (attr := simp)]
theorem pullback.sectionMap_fst (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S) :
    pullback.sectionMap p r σ hσ ≫ pullback.fst p r = r ≫ σ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullback.sectionMap_snd (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S) :
    pullback.sectionMap p r σ hσ ≫ pullback.snd p r = 𝟙 T :=
  pullback.lift_snd _ _ _

/-- Base-coordinate change retains the original section, including its
semilinear action on the source of the section. -/
@[reassoc]
theorem pullback.sectionMap_baseMap (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S) :
    pullback.sectionMap p s σ hσ ≫ pullback.baseMap p r s t ht =
      t ≫ pullback.sectionMap p r σ hσ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.baseMap_fst, pullback.sectionMap_fst]
    rw [← Category.assoc, ht]
  · simp only [Category.assoc, pullback.baseMap_snd, pullback.sectionMap_snd,
      pullback.sectionMap_snd_assoc, Category.comp_id]

end BaseMaps

section Factor

variable {Z W T S : C} (f : Z ⟶ T) (p : W ⟶ T)
    (g : T ⟶ T) (e : W ⟶ pullback f g)
    (he : e ≫ pullback.snd f g = p)
    (a j : S ⟶ T) (hja : j ≫ g = a)

/-- The genuine factor into the selected pullback, obtained from a map to the
appropriate conjugate. In applications `e` is a product component projection. -/
def pullback.conjugateFactor : pullback p j ⟶ pullback f a :=
  pullback.lift (pullback.fst p j ≫ e ≫ pullback.fst f g)
    (pullback.snd p j) (by
      calc
        _ = pullback.fst p j ≫ e ≫ (pullback.fst f g ≫ f) :=
          by simp only [Category.assoc]
        _ = pullback.fst p j ≫ e ≫ (pullback.snd f g ≫ g) := by
          rw [pullback.condition]
        _ = (pullback.fst p j ≫ (e ≫ pullback.snd f g)) ≫ g := by
          simp only [Category.assoc]
        _ = (pullback.fst p j ≫ p) ≫ g := by rw [he]
        _ = (pullback.snd p j ≫ j) ≫ g := by rw [pullback.condition]
        _ = pullback.snd p j ≫ a := by rw [Category.assoc, hja])

@[reassoc (attr := simp)]
theorem pullback.conjugateFactor_fst :
    pullback.conjugateFactor f p g e he a j hja ≫ pullback.fst f a =
      pullback.fst p j ≫ e ≫ pullback.fst f g :=
  pullback.lift_fst _ _ _

/-- The factor retains the original changed-base projection exactly. -/
@[reassoc (attr := simp)]
theorem pullback.conjugateFactor_snd :
    pullback.conjugateFactor f p g e he a j hja ≫ pullback.snd f a =
      pullback.snd p j :=
  pullback.lift_snd _ _ _

end Factor

end CategoryTheory.Limits
