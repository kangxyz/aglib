/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.Shapes.SectionPointLift
public import Aglib.AlgebraicGeometry.Morphisms.Immersion.ReducedFactor

/-! # Reduced section-point equations without separatedness

Every section of a scheme morphism is an immersion. The original reduced
source therefore factors through that section from support containment,
without requiring the ambient morphism to be separated.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- A reduced map supported on the original section satisfies its exact
section equation, without separatedness of the structure morphism. -/
theorem section_eq_of_reduced_range_subset
    {X S T : Scheme.{u}} (p : X ⟶ S)
    (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S) [IsReduced T]
    (η : T ⟶ X) (hη : Set.range η ⊆ Set.range σ) :
    η = (η ≫ p) ≫ σ := by
  let : IsImmersion (σ ≫ p) := by rw [hσ]; infer_instance
  let : IsImmersion σ := IsImmersion.of_comp σ p
  let l := liftReducedToImmersion σ η hη
  have hl : l ≫ σ = η := liftReducedToImmersion_fac σ η hη
  calc
    η = l ≫ σ := hl.symm
    _ = ((l ≫ σ) ≫ p) ≫ σ := by
      simp only [Category.assoc, hσ, Category.comp_id]
    _ = (η ≫ p) ≫ σ := by rw [hl]

/-- The literal pullback section condition follows from the original
X-coordinate's support for any reduced source. -/
theorem pullback_section_condition_of_reduced_range_subset
    {X S R T : Scheme.{u}} (p : X ⟶ S) (r : R ⟶ S)
    (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S) [IsReduced T]
    (z : T ⟶ pullback p r)
    (hz : Set.range (z ≫ pullback.fst p r) ⊆ Set.range σ) :
    z ≫ pullback.fst p r = (z ≫ pullback.snd p r ≫ r) ≫ σ := by
  calc
    z ≫ pullback.fst p r = ((z ≫ pullback.fst p r) ≫ p) ≫ σ :=
      section_eq_of_reduced_range_subset p σ hσ _ hz
    _ = (z ≫ pullback.snd p r ≫ r) ≫ σ :=
      congrArg (fun f => f ≫ σ)
        ((Category.assoc _ _ _).trans (congrArg (fun f => z ≫ f)
          (pullback.condition (f := p) (g := r))))

end AlgebraicGeometry.Scheme
