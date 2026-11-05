/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.SectionComponentAffineFiber

/-! # Section components inside an affine field pullback

Affineness of the one actual field pullback suffices. Neither the original
total scheme nor its base needs to be affine. The same original component
open is retained, using its actual base-change equation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- The original section-component restriction has an affine field pullback
whenever the whole original pullback at that field is affine. -/
theorem sectionComponent_fieldPullback_isAffine_of_isAffine_pullback
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (W : X.Opens) (hW : (W : Set X) = sectionComponentLocus f σ hσ)
    (K : Type u) [Field K] (b : Spec (CommRingCat.of K) ⟶ S)
    [IsAffine (pullback f b : Scheme.{u})] :
    IsAffine (pullback (W.ι ≫ f) b : Scheme.{u}) := by
  let Y : Scheme.{u} := pullback f b
  let a : Y ⟶ X := pullback.fst f b
  let q : Y ⟶ Spec (CommRingCat.of K) := pullback.snd f b
  let τ : Spec (CommRingCat.of K) ⟶ Y :=
    pullback.lift (b ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
  have hτq : τ ≫ q = 𝟙 _ := pullback.lift_snd ..
  have hτa : τ ≫ a = b ≫ σ := pullback.lift_fst ..
  let T := a ⁻¹ᵁ W
  have hT : (T : Set Y) = sectionComponentLocus q τ hτq := by
    change a ⁻¹' (W : Set X) = _
    rw [hW]
    exact sectionComponentLocus_preimage_of_isPullback f a q b
      (.of_hasPullback f b) σ hσ τ hτq hτa
  let : IsAffine Y := inferInstanceAs (IsAffine (pullback f b : Scheme.{u}))
  let : IsAffine T.toScheme := sectionComponent_isAffine_of_field K q τ hτq T hT
  have HT : IsPullback (a ∣_ W) (T.ι ≫ q) (W.ι ≫ f) b :=
    (isPullback_morphismRestrict a W).paste_vert (.of_hasPullback f b)
  exact IsAffine.of_isIso HT.isoPullback.inv

end AlgebraicGeometry.Scheme
