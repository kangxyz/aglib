/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.Shapes.SectionPointLift
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.ReducedFactor
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Reduced points lying on a section retain its scheme-theoretic equation

For a separated morphism the original section is a closed immersion. A
reduced point-shaped source whose image lies on this section factors through
it, so the original section equation follows as an equality of morphisms.
This supplies the hypothesis of the categorical whole-section lift.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- Reduced maps supported on the section factor through that same section. -/
theorem section_eq_of_range_subset
    {X S T : Scheme.{u}} (p : X ⟶ S) [IsSeparated p]
    (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S) [IsReduced T]
    (η : T ⟶ X) (hη : Set.range η ⊆ Set.range σ) :
    η = (η ≫ p) ≫ σ := by
  let : IsClosedImmersion (σ ≫ p) := by rw [hσ]; infer_instance
  let : IsClosedImmersion σ := IsClosedImmersion.of_comp σ p
  let l := liftReducedToClosed σ η hη
  have hl : l ≫ σ = η := liftReducedToClosed_fac σ η hη
  calc
    η = l ≫ σ := hl.symm
    _ = ((l ≫ σ) ≫ p) ≫ σ := by
      simp only [Category.assoc, hσ, Category.comp_id]
    _ = (η ≫ p) ≫ σ := by rw [hl]

/-- The literal pullback projections satisfy the section-point condition
once its original X-coordinate lies in the original section's image. -/
theorem pullback_section_condition_of_range_subset
    {X S R T : Scheme.{u}} (p : X ⟶ S) [IsSeparated p] (r : R ⟶ S)
    (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S) [IsReduced T]
    (z : T ⟶ pullback p r)
    (hz : Set.range (z ≫ pullback.fst p r) ⊆ Set.range σ) :
    z ≫ pullback.fst p r = (z ≫ pullback.snd p r ≫ r) ≫ σ := by
  calc
    z ≫ pullback.fst p r = ((z ≫ pullback.fst p r) ≫ p) ≫ σ :=
      section_eq_of_range_subset p σ hσ _ hz
    _ = (z ≫ pullback.snd p r ≫ r) ≫ σ := by
      exact congrArg (fun f => f ≫ σ)
        ((Category.assoc _ _ _).trans (congrArg (fun f => z ≫ f)
          (pullback.condition (f := p) (g := r))))

end AlgebraicGeometry.Scheme
