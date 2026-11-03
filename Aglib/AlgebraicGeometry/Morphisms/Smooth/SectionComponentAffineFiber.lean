/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.SectionComponentLocusPoints
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Whole field fibres of an affine-chart section component

The original component restriction is already an open subscheme. Over a
field it is a connected component, hence also closed, so its inclusion into
the original affine fibre is affine. No global Noetherian base is needed;
indeed closedness of connected components needs no Noetherian hypothesis.
The original component, section and specified point are not shrunk.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- An open section-component locus in an affine scheme over a field is
already affine: its range is the closed connected component of the section. -/
theorem sectionComponent_isAffine_of_field (K : Type u) [Field K]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (CommRingCat.of K))
    (σ : Spec (CommRingCat.of K) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (W : X.Opens) (hW : (W : Set X) = sectionComponentLocus f σ hσ) :
    IsAffine W.toScheme := by
  have hclosed : IsClosed (Set.range W.ι) := by
    rw [Opens.range_ι, hW, sectionComponentLocus_eq_connectedComponent_of_field K f σ hσ]
    exact isClosed_connectedComponent
  let : IsAffineHom W.ι :=
    isAffineHom_of_isInducing W.ι W.ι.isOpenEmbedding.isEmbedding.isInducing hclosed
  exact isAffine_of_isAffineHom W.ι

/-- Every original field fibre of the whole component restriction is affine.
Smoothness is used only for the actual component base-change equality. -/
theorem sectionComponent_fieldPullback_isAffine
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) [Smooth f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (W : X.Opens) (hW : (W : Set X) = sectionComponentLocus f σ hσ)
    (K : Type u) [Field K] (b : Spec (CommRingCat.of K) ⟶ S) :
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
