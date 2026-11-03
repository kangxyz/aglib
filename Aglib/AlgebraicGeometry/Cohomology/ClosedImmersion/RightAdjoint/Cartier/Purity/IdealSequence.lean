/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.Cartier.Purity.Global

/-!
# The original negative Cartier coefficient sequence

Regularity of the original positive Cartier section makes the existing
coefficient ideal sequence short exact. Its second map remains the literal
pullback-pushforward adjunction unit. The coefficient is an arbitrary module
sheaf: no quasicoherence or local freeness of the coefficient is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible

private theorem braidedIdealAction
    {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    {I : C} (a : I ⟶ 𝟙_ C) (M : C) :
    (β_ M I).hom ≫ (a ▷ M ≫ (λ_ M).hom) = M ◁ a ≫ (ρ_ M).hom := by
  rw [← Category.assoc, ← braiding_naturality_right, Category.assoc,
    braiding_tensorUnit_right]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Actual Cartier regularity makes the existing ideal-multiplication and
original quotient-unit sequence short exact. -/
theorem idealTensorQuotientSequence_shortExact {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (hI : IsLocallyRankOne X (idealModule i)) (M : X.Modules)
    [Mono ((cartierTensorSection i).app M)] :
    (idealTensorQuotientSequence i M).ShortExact where
  exact := idealTensorQuotientSequence_exact i M
  mono_f := by
    have hμ := cartierIdealAction_mono i hI M
    change Mono (idealInclusion i ▷ M ≫ (λ_ M).hom) at hμ
    let := hμ
    have h : (β_ M (idealModule i)).hom ≫
        (idealInclusion i ▷ M ≫ (λ_ M).hom) =
        M ◁ idealInclusion i ≫ (ρ_ M).hom :=
      braidedIdealAction (idealInclusion i) M
    change Mono (M ◁ idealInclusion i ≫ (ρ_ M).hom)
    exact h ▸ (inferInstance : Mono ((β_ M (idealModule i)).hom ≫
      (idealInclusion i ▷ M ≫ (λ_ M).hom)))
  epi_g := pullbackPushforwardUnit_epi i M

end AlgebraicGeometry.Scheme.Modules
