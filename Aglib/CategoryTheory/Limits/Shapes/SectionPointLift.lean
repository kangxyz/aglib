/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.Shapes.ConjugatePullbackFactor

/-! # All point-shaped maps on a section lift through its whole lift

The point shape is arbitrary. Its original pullback projections determine
it, so a whole lifted section supplies an actual lift of every such map.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
    {X S R G T : C} (p : X ⟶ S) (r : R ⟶ S)

/-- The original base coordinate followed by the unchanged whole lifted section. -/
def pullback.sectionLiftPoint (ρ : R ⟶ G) (z : T ⟶ pullback p r) : T ⟶ G :=
  z ≫ pullback.snd p r ≫ ρ

/-- The two actual pullback projections prove that the lifted point lies over
exactly the original map, not only over its underlying topological point. -/
@[reassoc]
theorem pullback.sectionLiftPoint_over
    (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S)
    (g : G ⟶ pullback p r) (ρ : R ⟶ G)
    (hρ : ρ ≫ g = pullback.sectionMap p r σ hσ)
    (z : T ⟶ pullback p r)
    (hz : z ≫ pullback.fst p r = (z ≫ pullback.snd p r ≫ r) ≫ σ) :
    pullback.sectionLiftPoint p r ρ z ≫ g = z := by
  apply pullback.hom_ext
  · simpa only [pullback.sectionLiftPoint, Category.assoc, hρ,
      pullback.sectionMap_fst] using hz.symm
  · simp only [pullback.sectionLiftPoint, Category.assoc, hρ,
      pullback.sectionMap_snd, Category.comp_id]

end CategoryTheory.Limits
