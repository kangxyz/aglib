/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence
public import Aglib.AlgebraicGeometry.Blowup.ClosedImmersion
public import Aglib.AlgebraicGeometry.IdealSheaf.ClosedExtension

/-!
# Extending actual blowup sequences along closed immersions

Each centre is extended by its actual pushforward ideal. The native closed
blowup comparison supplies the next closed immersion and its literal triangle.
No nonflat base-change identity or arbitrary proper-extension principle is used.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Blowup.AdmissibleSequence

/-- An actual admissible sequence on a closed subscheme extends to an ambient
admissible sequence, with a closed comparison and the original base triangle. -/
theorem exists_closed_extension {X Z T : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (V : X.Opens) {β : T ⟶ Z}
    (hβ : AdmissibleSequence (i ⁻¹ᵁ V) β) :
    ∃ (X' : Scheme.{u}) (α : X' ⟶ X) (j : T ⟶ X'),
      AdmissibleSequence V α ∧ IsClosedImmersion j ∧ j ≫ α = β ≫ i := by
  induction hβ with
  | id =>
      exact ⟨X, 𝟙 X, i, .id, inferInstance, by simp⟩
  | @step Y δ hδ J B hJ ih =>
      obtain ⟨X', α, j, hα, hj, he⟩ := ih
      let : IsClosedImmersion j := hj
      have hp : j ⁻¹ᵁ (α ⁻¹ᵁ V) = δ ⁻¹ᵁ (i ⁻¹ᵁ V) := by
        rw [← Hom.comp_preimage, he, Hom.comp_preimage]
      have hJ' : J.comap (j ⁻¹ᵁ (α ⁻¹ᵁ V)).ι = ⊤ := by
        rw [hp]
        exact hJ
      let K := J.map j
      let D := blowupDatum K
      have hK : K.comap j = J := J.comap_map_of_isClosedImmersion j
      have hKV : K.comap (α ⁻¹ᵁ V).ι = ⊤ :=
        J.map_comap_eq_top_of_comap_eq_top j (α ⁻¹ᵁ V) hJ'
      let k := BaseChange.map j hK D B
      have hk : IsClosedImmersion k := BaseChange.map_isClosedImmersion j hK D B
      refine ⟨D.Y, D.map ≫ α, k, .step hα K D hKV, hk, ?_⟩
      rw [← Category.assoc, BaseChange.map_triangle, Category.assoc, he, Category.assoc]
  | iso hδ e ih =>
      obtain ⟨X', α, j, hα, hj, he⟩ := ih
      let : IsClosedImmersion j := hj
      refine ⟨X', α, e.hom ≫ j, hα, inferInstance, ?_⟩
      rw [Category.assoc, he, Category.assoc]

end AlgebraicGeometry.Scheme.Blowup.AdmissibleSequence
