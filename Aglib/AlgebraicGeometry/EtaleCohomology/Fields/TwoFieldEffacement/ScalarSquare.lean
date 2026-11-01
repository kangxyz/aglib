/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.CompatibleClosure

/-! # Original scalar-extension maps into a specified source-stage pullback

The target is the already constructed source-stage scheme. The universal map
from the literal new coefficient pullback and its field-tower equation retain
that scheme, its original projections, and the original coefficient arrows.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u

variable {U V S F L : Scheme.{u}}
  (p : U ⟶ S) (v : V ⟶ U) (q : V ⟶ F) (a : F ⟶ S)
  (H : IsPullback v q p a) (b : L ⟶ S) (i : L ⟶ F) (hi : i ≫ a = b)

/-- The original pullback universal map to the unchanged source-stage scheme. -/
def scalarSquareLift : pullback p b ⟶ V :=
  H.lift (pullback.fst p b) (pullback.snd p b ≫ i) (by
    rw [Category.assoc, hi]
    exact pullback.condition)

@[reassoc] theorem scalarSquareLift_original :
    scalarSquareLift p v q a H b i hi ≫ v = pullback.fst p b := H.lift_fst _ _ _

@[reassoc] theorem scalarSquareLift_field :
    scalarSquareLift p v q a H b i hi ≫ q = pullback.snd p b ≫ i := H.lift_snd _ _ _

/-- The same universal map is the actual base change of the new coefficient arrow. -/
theorem scalarSquareLift_isPullback :
    IsPullback (scalarSquareLift p v q a H b i hi) (pullback.snd p b) q i := by
  apply IsPullback.of_right (h₁₂ := v) (h₂₂ := a)
  · rw [scalarSquareLift_original, hi]
    exact IsPullback.of_hasPullback _ _
  · exact scalarSquareLift_field p v q a H b i hi
  · exact H

/-- The whole field-tower equation is proved on the original pullback projections,
without changing the selected source-stage scheme. -/
theorem scalarSquareLift_tower {Ω : Scheme.{u}}
    (bΩ : Ω ⟶ S) (iΩ : Ω ⟶ F) (hiΩ : iΩ ≫ a = bΩ)
    (d : Ω ⟶ L) (hd : d ≫ b = bΩ) (hdi : d ≫ i = iΩ) :
    pullback.map p bΩ p b (𝟙 U) d (𝟙 S)
        (by simp) (by simpa only [Category.comp_id] using hd.symm) ≫
      scalarSquareLift p v q a H b i hi = scalarSquareLift p v q a H bΩ iΩ hiΩ := by
  apply H.hom_ext
  · simp only [Category.assoc, scalarSquareLift_original, pullback.map,
      pullback.lift_fst, Category.comp_id]
  · simp only [Category.assoc, scalarSquareLift_field, pullback.map,
      pullback.lift_snd_assoc, hdi]

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
