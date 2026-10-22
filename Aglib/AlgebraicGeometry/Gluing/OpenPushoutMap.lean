/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Gluing.OpenImmersion
public import Aglib.AlgebraicGeometry.Morphisms.OpenImmersion.Cartesian

/-!
# Cartesian maps of actual open pushouts

A cartesian map of open gluing spans gives the literal native `pushout.map`.
Its two open-chart squares are cartesian. In particular, affine maps on both
charts give an affine map on the glued schemes. No replacement pushout or
separatedness, quasi-compactness, or Noetherian hypothesis is introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.OpenPushoutMap

variable {W U V W' U' V' : Scheme.{u}}
  (f : W ⟶ U) (g : W ⟶ V) (f' : W' ⟶ U') (g' : W' ⟶ V')
  [IsOpenImmersion f] [IsOpenImmersion g]
  [IsOpenImmersion f'] [IsOpenImmersion g']
  (a : W ⟶ W') (b : U ⟶ U') (c : V ⟶ V')
  (hf : f ≫ b = a ≫ f') (hg : g ≫ c = a ≫ g')

/-- The left chart preimage is controlled by preservation of the right overlap. -/
theorem preimage_inl_of_preimage_eq (hv : c ⁻¹ᵁ g'.opensRange = g.opensRange) :
    pushout.map f g f' g' b c a hf hg ⁻¹ᵁ (pushout.inl f' g').opensRange =
      (pushout.inl f g).opensRange := by
  ext z
  change (∃ x, pushout.inl f' g' x = pushout.map f g f' g' b c a hf hg z) ↔
    ∃ x, pushout.inl f g x = z
  constructor
  · rintro ⟨x, hx⟩
    rcases openPushout_covered f g z with ⟨x', rfl⟩ | ⟨y, rfl⟩
    · exact ⟨x', rfl⟩
    · have he : pushout.inl f' g' x = pushout.inr f' g' (c y) := by
        simpa only [← Hom.comp_apply, pushout.map, pushout.inr_desc] using hx
      obtain ⟨t, _, ht⟩ := (OpenNormalizationGluing.left_eq_right_iff f' g' x (c y)).mp he
      have hy : y ∈ g.opensRange := by
        rw [← hv]
        exact ⟨t, ht⟩
      obtain ⟨t', rfl⟩ := hy
      refine ⟨f t', ?_⟩
      rw [← Hom.comp_apply, ← Hom.comp_apply, pushout.condition]
  · rintro ⟨x, rfl⟩
    refine ⟨b x, ?_⟩
    simp only [← Hom.comp_apply, pushout.map, pushout.inl_desc]

/-- The right chart preimage is controlled by preservation of the left overlap. -/
theorem preimage_inr_of_preimage_eq (hu : b ⁻¹ᵁ f'.opensRange = f.opensRange) :
    pushout.map f g f' g' b c a hf hg ⁻¹ᵁ (pushout.inr f' g').opensRange =
      (pushout.inr f g).opensRange := by
  ext z
  change (∃ y, pushout.inr f' g' y = pushout.map f g f' g' b c a hf hg z) ↔
    ∃ y, pushout.inr f g y = z
  constructor
  · rintro ⟨y, hy⟩
    rcases openPushout_covered f g z with ⟨x, rfl⟩ | ⟨y', rfl⟩
    · have he : pushout.inl f' g' (b x) = pushout.inr f' g' y := by
        symm
        simpa only [← Hom.comp_apply, pushout.map, pushout.inl_desc] using hy
      obtain ⟨t, ht, _⟩ := (OpenNormalizationGluing.left_eq_right_iff f' g' (b x) y).mp he
      have hx : x ∈ f.opensRange := by
        rw [← hu]
        exact ⟨t, ht⟩
      obtain ⟨t', rfl⟩ := hx
      refine ⟨g t', ?_⟩
      rw [← Hom.comp_apply, ← Hom.comp_apply, pushout.condition]
    · exact ⟨y', rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨c y, ?_⟩
    simp only [← Hom.comp_apply, pushout.map, pushout.inr_desc]

/-- The inverse image of the original left chart is the original left chart.
Only cartesianness of the other overlap square is needed. -/
theorem preimage_inl (Hg : IsPullback a g g' c) :
    pushout.map f g f' g' b c a hf hg ⁻¹ᵁ (pushout.inl f' g').opensRange =
      (pushout.inl f g).opensRange :=
  preimage_inl_of_preimage_eq f g f' g' a b c hf hg
    (Hom.opensRange_of_isPullback g a c g' Hg.flip).symm

/-- The inverse image of the original right chart is the original right chart.
Only cartesianness of the other overlap square is needed. -/
theorem preimage_inr (Hf : IsPullback a f f' b) :
    pushout.map f g f' g' b c a hf hg ⁻¹ᵁ (pushout.inr f' g').opensRange =
      (pushout.inr f g).opensRange :=
  preimage_inr_of_preimage_eq f g f' g' a b c hf hg
    (Hom.opensRange_of_isPullback f a b f' Hf.flip).symm

/-- The native pushout map is cartesian on its original left open chart. -/
theorem isPullback_inl (Hg : IsPullback a g g' c) :
    IsPullback b (pushout.inl f g) (pushout.inl f' g')
      (pushout.map f g f' g' b c a hf hg) :=
  IsOpenImmersion.isPullback b _ _ _ (pushout.inl_desc _ _ _)
    (preimage_inl f g f' g' a b c hf hg Hg)

/-- The native pushout map is cartesian on its original right open chart. -/
theorem isPullback_inr (Hf : IsPullback a f f' b) :
    IsPullback c (pushout.inr f g) (pushout.inr f' g')
      (pushout.map f g f' g' b c a hf hg) :=
  IsOpenImmersion.isPullback c _ _ _ (pushout.inr_desc _ _ _)
    (preimage_inr f g f' g' a b c hf hg Hf)

/-- Affineness of both chart maps makes the literal map of open pushouts
an affine morphism. -/
theorem isAffineHom (Hf : IsPullback a f f' b) (Hg : IsPullback a g g' c)
    [IsAffineHom b] [IsAffineHom c] :
    IsAffineHom (pushout.map f g f' g' b c a hf hg) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsAffineHom)
    (OpenNormalizationGluing.twoChartCover f' g')
  intro k
  cases k
  · change IsAffineHom (pullback.snd (pushout.map f g f' g' b c a hf hg)
      (pushout.inl f' g'))
    rw [← (isPullback_inl f g f' g' a b c hf hg Hg).flip.isoPullback_inv_snd]
    infer_instance
  · change IsAffineHom (pullback.snd (pushout.map f g f' g' b c a hf hg)
      (pushout.inr f' g'))
    rw [← (isPullback_inr f g f' g' a b c hf hg Hf).flip.isoPullback_inv_snd]
    infer_instance

end AlgebraicGeometry.Scheme.OpenPushoutMap
