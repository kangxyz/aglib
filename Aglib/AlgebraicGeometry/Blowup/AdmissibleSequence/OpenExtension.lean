/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence
public import Aglib.AlgebraicGeometry.IdealSheaf.OpenExtension
public import Aglib.AlgebraicGeometry.Blowup.FlatBaseChange
public import Aglib.AlgebraicGeometry.Blowup.Construction

/-!
# Extending actual blowup sequences from open subschemes

Each centre is extended by its native pushforward ideal. Flat base change
identifies the original blowup with the restriction of the extended blowup.
The resulting comparison is an actual Cartesian square, not just a commuting
triangle or a claim about the underlying point sets.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Blowup.AdmissibleSequence

/-- A sequence on a quasi-compact open extends to an ambient admissible sequence
whose actual restriction is the original sequence. No Noetherian hypothesis is
needed for this extension and Cartesian comparison. -/
theorem exists_open_extension {X Z T : Scheme.{u}} (q : Z ⟶ X)
    [IsOpenImmersion q] [QuasiCompact q] (U : X.Opens) {β : T ⟶ Z}
    (hβ : AdmissibleSequence (q ⁻¹ᵁ U) β) :
    ∃ (X' : Scheme.{u}) (α : X' ⟶ X) (j : T ⟶ X'),
      AdmissibleSequence U α ∧ IsPullback j β α q := by
  induction hβ with
  | id =>
      exact ⟨X, 𝟙 X, q, .id, IsPullback.of_vert_isIso ⟨by simp⟩⟩
  | @step Y δ hδ J B hJ ih =>
      obtain ⟨X', α, j, hα, hj⟩ := ih
      let : IsOpenImmersion j := MorphismProperty.of_isPullback hj.flip inferInstance
      let : QuasiCompact j := MorphismProperty.of_isPullback hj.flip inferInstance
      have hp : j ⁻¹ᵁ (α ⁻¹ᵁ U) = δ ⁻¹ᵁ (q ⁻¹ᵁ U) := by
        rw [← Hom.comp_preimage, hj.w, Hom.comp_preimage]
      have hJ' : J.comap (j ⁻¹ᵁ (α ⁻¹ᵁ U)).ι = ⊤ := by
        rw [hp]
        exact hJ
      let K := J.map j
      let D := Blowup.blowupDatum K
      have hK : K.comap j = J := J.comap_map_of_isOpenImmersion j
      have hKU : K.comap (α ⁻¹ᵁ U).ι = ⊤ :=
        J.map_comap_eq_top_of_comap_eq_top j (α ⁻¹ᵁ U) hJ'
      let k := BaseChange.map j hK D B
      have hk : IsPullback k B.map D.map j :=
        BaseChange.isPullback_of_flat j inferInstance hK D B
      exact ⟨D.Y, D.map ≫ α, k, .step hα K D hKU, hk.paste_vert hj⟩
  | iso hδ e ih =>
      obtain ⟨X', α, j, hα, hj⟩ := ih
      refine ⟨X', α, e.hom ≫ j, hα, ?_⟩
      exact hj.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp) (by simp) (by simp)

end AlgebraicGeometry.Scheme.Blowup.AdmissibleSequence
