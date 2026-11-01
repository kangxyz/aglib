/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Relative normalization retains an original finite open restriction

The square concerns the literal original finite morphism and both native
normalization arrows. Smooth base change of normalization and the trivial
normalization of an integral morphism produce its actual pullback witness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Relative normalization of a finite map followed by an open immersion
restricts to exactly the original finite map, not a newly chosen model. -/
theorem isPullback_toNormalization_of_finite_open
    {V U X : Scheme.{u}} (v : V ⟶ U) [IsFinite v]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    IsPullback (v ≫ j).toNormalization v (v ≫ j).fromNormalization j := by
  let f := v ≫ j
  have H : IsPullback (𝟙 V) v f j :=
    IsPullback.of_horiz_isIso_mono ⟨by simp [f]⟩
  let q := pullback.snd f j
  let : IsFinite q := by
    rw [show q = H.isoPullback.inv ≫ v from H.isoPullback_inv_snd.symm]
    infer_instance
  let e : V ≅ pullback f.fromNormalization j :=
    H.isoPullback ≪≫ asIso q.toNormalization ≪≫ asIso (f.normalizationPullback j)
  apply IsPullback.of_iso_pullback ⟨f.toNormalization_fromNormalization⟩ e
  · change H.isoPullback.hom ≫ q.toNormalization ≫ f.normalizationPullback j ≫
        pullback.fst f.fromNormalization j = f.toNormalization
    rw [toNormalization_normalizationPullback_fst]
    simp only [← Category.assoc, H.isoPullback_hom_fst, Category.id_comp]
  · change H.isoPullback.hom ≫ q.toNormalization ≫ f.normalizationPullback j ≫
        pullback.snd f.fromNormalization j = v
    rw [normalizationPullback_snd]
    change H.isoPullback.hom ≫ (q.toNormalization ≫ q.fromNormalization) = v
    rw [toNormalization_fromNormalization]
    exact H.isoPullback_hom_snd

end AlgebraicGeometry.Scheme.Hom
