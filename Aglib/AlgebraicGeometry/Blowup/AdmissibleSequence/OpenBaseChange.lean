/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence
public import Aglib.AlgebraicGeometry.Blowup.FlatBaseChange

/-!
# Restricting actual admissible sequences to open subschemes

Each recorded blowup is restricted using its actual flat pullback datum.
The comparison is Cartesian, not an arbitrary domination morphism.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Blowup.AdmissibleSequence

/-- An actual admissible sequence restricts to an open subscheme, with the
literal pulled-back protected open and an actual Cartesian comparison. -/
theorem exists_open_baseChange {X T Y : Scheme.{u}} {U : X.Opens} {β : T ⟶ X}
    (hβ : AdmissibleSequence U β) (q : Y ⟶ X) [IsOpenImmersion q] :
    ∃ (Y' : Scheme.{u}) (γ : Y' ⟶ Y) (j : Y' ⟶ T),
      AdmissibleSequence (q ⁻¹ᵁ U) γ ∧ IsPullback j γ β q := by
  induction hβ with
  | id =>
      exact ⟨Y, 𝟙 Y, q, .id, IsPullback.of_vert_isIso ⟨by simp⟩⟩
  | @step T δ hδ J B hJ ih =>
      obtain ⟨Y', γ, j, hγ, hj⟩ := ih
      let : IsOpenImmersion j := MorphismProperty.of_isPullback hj.flip inferInstance
      let D := flatPullbackDatum B j
      have hp : γ ⁻¹ᵁ (q ⁻¹ᵁ U) = j ⁻¹ᵁ (δ ⁻¹ᵁ U) := by
        rw [← Hom.comp_preimage, ← hj.w, Hom.comp_preimage]
      have ht : (J.comap j).comap (γ ⁻¹ᵁ (q ⁻¹ᵁ U)).ι = ⊤ := by
        rw [hp, ← IdealSheafData.comap_comp, ← morphismRestrict_ι,
          IdealSheafData.comap_comp, hJ, IdealSheafData.comap_top]
      have hD : IsPullback (pullback.fst B.map j) D.map B.map j :=
        IsPullback.of_hasPullback _ _
      exact ⟨D.Y, D.map ≫ γ, pullback.fst B.map j,
        .step hγ _ D ht, hD.paste_vert hj⟩
  | iso hδ e ih =>
      obtain ⟨Y', γ, j, hγ, hj⟩ := ih
      refine ⟨Y', γ, j ≫ e.inv, hγ, ?_⟩
      exact hj.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
        (by simp) (by simp) (by simp) (by simp)

end AlgebraicGeometry.Scheme.Blowup.AdmissibleSequence
