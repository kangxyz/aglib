/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Gluing.OpenImmersion
public import Aglib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Schematic density in an open pushout

A schematically dense overlap on one chart makes the other chart
schematically dense in the glued scheme. This is native open-cover locality,
not an inference from topological density.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- The left chart is schematically dense when the overlap is schematically
dense in the right chart. No quasi-compactness or reducedness is needed. -/
theorem pushout_inl_isSchemeTheoreticallyDominant
    {W X Y : Scheme.{u}} (f : W ⟶ X) (g : W ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsSchemeTheoreticallyDominant g] :
    IsSchemeTheoreticallyDominant (pushout.inl f g) := by
  let C := OpenNormalizationGluing.twoChartCover f g
  let A : Bool → Scheme.{u} := fun b ↦ if b then W else X
  let k : ∀ b, A b ⟶ C.X b := fun b ↦ by
    cases b
    · exact 𝟙 X
    · exact g
  apply isSchemeTheoreticallyDominant_of_openCover_ranges (pushout.inl f g) C A k
  · intro b
    cases b
    · change IsSchemeTheoreticallyDominant (𝟙 X)
      infer_instance
    · change IsSchemeTheoreticallyDominant g
      infer_instance
  · intro b
    cases b
    · change Set.range (𝟙 X ≫ pushout.inl f g) ⊆ Set.range (pushout.inl f g)
      simp
    · change Set.range (g ≫ pushout.inr f g) ⊆ Set.range (pushout.inl f g)
      rw [← pushout.condition]
      exact Set.range_comp_subset_range f (pushout.inl f g)

end AlgebraicGeometry.Scheme
