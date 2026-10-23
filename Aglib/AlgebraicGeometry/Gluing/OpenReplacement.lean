/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Gluing.OpenPushoutMap
public import Aglib.AlgebraicGeometry.Gluing.OpenUnionPushout
public import Aglib.AlgebraicGeometry.Properties.Regular.OpenCover
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Replacing one open chart by a proper contraction

For open immersions `f : T ⟶ U` and `g : T ⟶ W`, a morphism `b : U ⟶ V`
whose composite `f ≫ b` is an open immersion gives the native map
`pushout f g ⟶ pushout (f ≫ b) g`. The left chart is always cartesian.
The right chart is cartesian when the overlap square for `b` is cartesian,
equivalently when the overlap is its exact inverse-image open. Under this
explicit condition, properness of `b` implies properness of the glued map.

For two actual opens covering `X`, the source pushout is transported to the
original `X`. The target is locally Noetherian and has regular stalks when
its two charts do. No surface contraction or relative ampleness is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.OpenReplacement

/-- A closed subscheme of one chart, disjoint from the overlap, remains a
closed subscheme of the actual open pushout. -/
theorem isClosedImmersion_inl_of_disjoint {T V W D : Scheme.{u}}
    (a : T ⟶ V) (g : T ⟶ W) [IsOpenImmersion a] [IsOpenImmersion g]
    (c : D ⟶ V) [IsClosedImmersion c]
    (hdis : Disjoint (Set.range c) (Set.range a)) :
    IsClosedImmersion (c ≫ pushout.inl a g) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (OpenNormalizationGluing.twoChartCover a g)
  intro k
  cases k
  · change IsClosedImmersion
      (pullback.snd (c ≫ pushout.inl a g) (pushout.inl a g))
    have Hleft : IsPullback c (𝟙 D) (pushout.inl a g) (c ≫ pushout.inl a g) :=
      IsPullback.of_vert_isIso_mono ⟨by simp⟩
    rw [← Hleft.flip.isoPullback_inv_snd]
    infer_instance
  · change IsClosedImmersion
      (pullback.snd (c ≫ pushout.inl a g) (pushout.inr a g))
    have hdis' : Disjoint (Set.range (c ≫ pushout.inl a g))
        (Set.range (pushout.inr a g)) := by
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨d, rfl⟩ ⟨w, hw⟩
      have he : pushout.inl a g (c d) = pushout.inr a g w := by
        simpa only [Hom.comp_apply] using hw.symm
      obtain ⟨t, ht, -⟩ := (OpenNormalizationGluing.left_eq_right_iff a g (c d) w).mp he
      exact Set.disjoint_left.mp hdis ⟨d, rfl⟩ ⟨t, ht⟩
    let : IsEmpty ↑(pullback (c ≫ pushout.inl a g) (pushout.inr a g) : Scheme.{u}) :=
      Scheme.isEmpty_pullback _ _ hdis'
    infer_instance

section Span

variable {T U W V : Scheme.{u}} (f : T ⟶ U) (g : T ⟶ W) (b : U ⟶ V)
  [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion (f ≫ b)]

/-- The original open pushout. -/
abbrev source : Scheme.{u} := pushout f g

/-- Replace `U` by `V` using the actual composite overlap map. -/
abbrev target : Scheme.{u} := pushout (f ≫ b) g

/-- The native map of open pushouts, induced by `b` and the identity of `W`. -/
def map : source f g ⟶ target f g b :=
  pushout.map f g (f ≫ b) g b (𝟙 W) (𝟙 T) (by simp) (by simp)

@[reassoc (attr := simp)] theorem inl_map :
    pushout.inl f g ≫ map f g b = b ≫ pushout.inl (f ≫ b) g := by
  simp only [map, pushout.map, pushout.inl_desc]

@[reassoc (attr := simp)] theorem inr_map :
    pushout.inr f g ≫ map f g b = pushout.inr (f ≫ b) g := by
  simp only [map, pushout.map, pushout.inr_desc, Category.id_comp]

/-- The exact-preimage condition is sufficient for the overlap square. -/
theorem overlap_isPullback_of_preimage
    (hpre : b ⁻¹ᵁ (f ≫ b).opensRange = f.opensRange) :
    IsPullback (𝟙 T) f (f ≫ b) b :=
  IsOpenImmersion.isPullback _ _ _ _ (by simp) hpre

/-- The overlap square gives the exact inverse-image condition. -/
theorem overlap_preimage (H : IsPullback (𝟙 T) f (f ≫ b) b) :
    b ⁻¹ᵁ (f ≫ b).opensRange = f.opensRange :=
  (Hom.opensRange_of_isPullback f (𝟙 T) b (f ≫ b) H.flip).symm

/-- Over the replacement chart, the actual glued map is the original `b`. -/
theorem isPullback_inl :
    IsPullback b (pushout.inl f g) (pushout.inl (f ≫ b) g) (map f g b) :=
  OpenPushoutMap.isPullback_inl f g (f ≫ b) g (𝟙 T) b (𝟙 W)
    (by simp) (by simp) (IsPullback.id_horiz g)

/-- Over the unchanged chart, the actual glued map is the identity. -/
theorem isPullback_inr (H : IsPullback (𝟙 T) f (f ≫ b) b) :
    IsPullback (𝟙 W) (pushout.inr f g) (pushout.inr (f ≫ b) g) (map f g b) :=
  OpenPushoutMap.isPullback_inr f g (f ≫ b) g (𝟙 T) b (𝟙 W)
    (by simp) (by simp) H

/-- Properness follows on the two actual target charts. -/
theorem isProper_map [IsProper b] (H : IsPullback (𝟙 T) f (f ≫ b) b) :
    IsProper (map f g b) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsProper)
    (OpenNormalizationGluing.twoChartCover (f ≫ b) g)
  intro k
  cases k
  · change IsProper (pullback.snd (map f g b) (pushout.inl (f ≫ b) g))
    rw [← (isPullback_inl f g b).flip.isoPullback_inv_snd]
    infer_instance
  · change IsProper (pullback.snd (map f g b) (pushout.inr (f ≫ b) g))
    rw [← (isPullback_inr f g b H).flip.isoPullback_inv_snd]
    infer_instance

/-- The canonical base change to the unchanged chart is an isomorphism. -/
theorem isIso_pullback_unchanged (H : IsPullback (𝟙 T) f (f ≫ b) b) :
    IsIso (pullback.snd (map f g b) (pushout.inr (f ≫ b) g)) := by
  rw [← isIso_comp_left_iff (isPullback_inr f g b H).flip.isoPullback.hom]
  simpa using (inferInstance : IsIso (𝟙 W))

/-- The literal restriction to the unchanged target open is an isomorphism. -/
theorem isIso_restrict_unchanged (H : IsPullback (𝟙 T) f (f ≫ b) b) :
    IsIso (map f g b ∣_ (pushout.inr (f ≫ b) g).opensRange) := by
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (morphismRestrictOpensRange (map f g b) (pushout.inr (f ≫ b) g))).mpr
      (isIso_pullback_unchanged f g b H)

omit [IsOpenImmersion f] in
/-- The target inherits local Noetherianity from its actual two charts. -/
theorem isLocallyNoetherian_target [IsLocallyNoetherian V] [IsLocallyNoetherian W] :
    IsLocallyNoetherian (target f g b) := by
  apply (isLocallyNoetherian_iff_openCover
    (OpenNormalizationGluing.twoChartCover (f ≫ b) g)).mpr
  intro k
  cases k
  · change IsLocallyNoetherian V
    infer_instance
  · change IsLocallyNoetherian W
    infer_instance

omit [IsOpenImmersion f] in
/-- The target inherits regularity of its actual stalks from its two charts. -/
theorem regularStalks_target (hV : RegularStalks V) (hW : RegularStalks W) :
    RegularStalks (target f g b) := by
  intro z
  rcases openPushout_covered (f ≫ b) g z with ⟨v, rfl⟩ | ⟨w, rfl⟩
  · exact RegularStalks.at_image (pushout.inl (f ≫ b) g) hV v
  · exact RegularStalks.at_image (pushout.inr (f ≫ b) g) hW w

/-- Away from the overlap, the set-theoretic fibre is the original fibre of `b`. -/
theorem fibre_inl (v : V) (hv : ∀ t : T, (f ≫ b) t ≠ v) (z : source f g) :
    map f g b z = pushout.inl (f ≫ b) g v ↔
      ∃ x : U, b x = v ∧ pushout.inl f g x = z := by
  simpa only [map, pushout.map, Category.id_comp,
    OpenNormalizationGluing.normalizationMap] using
    (OpenNormalizationGluing.normalization_fibre (f ≫ b) g f b rfl v hv z)

end Span

namespace OfOpens

variable {X : Scheme.{u}} (U W : X.Opens) (hcover : U ⊔ W = ⊤)

/-- The actual scheme `X` is the native pushout of its two specified opens. -/
def sourceIso : X ≅ source (W.ι ∣_ U) (W.ι ⁻¹ᵁ U).ι :=
  (Scheme.isPushout_opens_of_sup_eq_top U W hcover).isoPushout

variable {V : Scheme.{u}} (b : U.toScheme ⟶ V)
  [IsOpenImmersion ((W.ι ∣_ U) ≫ b)]

/-- The actual replacement of `U` in `X` by `V`. -/
abbrev target : Scheme.{u} :=
  OpenReplacement.target (W.ι ∣_ U) (W.ι ⁻¹ᵁ U).ι b

/-- The map has the original scheme as its literal source. -/
def map : X ⟶ target U W b :=
  (sourceIso U W hcover).hom ≫
    OpenReplacement.map (W.ι ∣_ U) (W.ι ⁻¹ᵁ U).ι b

@[reassoc (attr := simp)] theorem left_map :
    U.ι ≫ map U W hcover b = b ≫ pushout.inl ((W.ι ∣_ U) ≫ b) (W.ι ⁻¹ᵁ U).ι := by
  simp only [map, ← Category.assoc, sourceIso, IsPushout.inl_isoPushout_hom,
    OpenReplacement.inl_map]

@[reassoc (attr := simp)] theorem right_map :
    W.ι ≫ map U W hcover b = pushout.inr ((W.ι ∣_ U) ≫ b) (W.ι ⁻¹ᵁ U).ι := by
  simp only [map, ← Category.assoc, sourceIso, IsPushout.inr_isoPushout_hom,
    OpenReplacement.inr_map]

/-- The replacement chart square is cartesian with the original inclusion of `U`. -/
theorem isPullback_left :
    IsPullback b U.ι (pushout.inl ((W.ι ∣_ U) ≫ b) (W.ι ⁻¹ᵁ U).ι)
      (map U W hcover b) := by
  apply (OpenReplacement.isPullback_inl (W.ι ∣_ U) (W.ι ⁻¹ᵁ U).ι b).of_iso
    (Iso.refl _) (Iso.refl _) (sourceIso U W hcover).symm (Iso.refl _)
  · simp
  · simp [sourceIso]
  · simp
  · simp [map]

/-- The unchanged chart square is cartesian with the original inclusion of `W`. -/
theorem isPullback_right
    (H : IsPullback (𝟙 (W.ι ⁻¹ᵁ U).toScheme) (W.ι ∣_ U) ((W.ι ∣_ U) ≫ b) b) :
    IsPullback (𝟙 W.toScheme) W.ι
      (pushout.inr ((W.ι ∣_ U) ≫ b) (W.ι ⁻¹ᵁ U).ι) (map U W hcover b) := by
  apply (OpenReplacement.isPullback_inr (W.ι ∣_ U) (W.ι ⁻¹ᵁ U).ι b H).of_iso
    (Iso.refl _) (Iso.refl _) (sourceIso U W hcover).symm (Iso.refl _)
  · simp
  · simp [sourceIso]
  · simp
  · simp [map]

/-- A proper local contraction extends to a proper morphism out of the original `X`. -/
theorem isProper_map [IsProper b]
    (H : IsPullback (𝟙 (W.ι ⁻¹ᵁ U).toScheme) (W.ι ∣_ U) ((W.ι ∣_ U) ≫ b) b) :
    IsProper (map U W hcover b) := by
  let := OpenReplacement.isProper_map (W.ι ∣_ U) (W.ι ⁻¹ᵁ U).ι b H
  dsimp [map]
  infer_instance

/-- The proper extension is unchanged over the target copy of `W`. -/
theorem isIso_restrict_unchanged
    (H : IsPullback (𝟙 (W.ι ⁻¹ᵁ U).toScheme) (W.ι ∣_ U) ((W.ι ∣_ U) ≫ b) b) :
    IsIso (map U W hcover b ∣_
      (pushout.inr ((W.ι ∣_ U) ≫ b) (W.ι ⁻¹ᵁ U).ι).opensRange) := by
  have hp : IsIso (pullback.snd (map U W hcover b)
      (pushout.inr ((W.ι ∣_ U) ≫ b) (W.ι ⁻¹ᵁ U).ι)) := by
    rw [← isIso_comp_left_iff (isPullback_right U W hcover b H).flip.isoPullback.hom]
    simpa using (inferInstance : IsIso (𝟙 W.toScheme))
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (morphismRestrictOpensRange (map U W hcover b)
      (pushout.inr ((W.ι ∣_ U) ≫ b) (W.ι ⁻¹ᵁ U).ι))).mpr hp

/-- Local Noetherianity of the two replacement charts suffices. -/
theorem isLocallyNoetherian_target [IsLocallyNoetherian V] [IsLocallyNoetherian W.toScheme] :
    IsLocallyNoetherian (target U W b) :=
  OpenReplacement.isLocallyNoetherian_target (W.ι ∣_ U) (W.ι ⁻¹ᵁ U).ι b

/-- Regular stalks on the two replacement charts suffice. -/
theorem regularStalks_target (hV : RegularStalks V) (hW : RegularStalks W.toScheme) :
    RegularStalks (target U W b) :=
  OpenReplacement.regularStalks_target (W.ι ∣_ U) (W.ι ⁻¹ᵁ U).ι b hV hW

end OfOpens

end AlgebraicGeometry.Scheme.OpenReplacement
