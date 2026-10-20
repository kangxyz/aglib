/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Gluing schemes along open immersions

Source: `R5Lab.Aglib.AlgebraicGeometry.Gluing.OpenImmersion`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `cabc8aa7f82dc16cf30573891b94b679206116679a2f8c3122879d25a86b7682`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme

theorem openPushout_covered {W U V : Scheme.{u}} (f : W ⟶ U) (g : W ⟶ V)
    [IsOpenImmersion f] [IsOpenImmersion g] (z : (pushout f g : Scheme.{u})) :
    (∃ x, pushout.inl f g x = z) ∨ ∃ y, pushout.inr f g y = z := by
  obtain ⟨i, x, h⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span f g) z
  cases i with
  | none =>
    left
    refine ⟨f x, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    change (f ≫ colimit.ι (span f g) WalkingSpan.left) x = z
    rw [show f ≫ colimit.ι (span f g) WalkingSpan.left =
      colimit.ι (span f g) WalkingSpan.zero from colimit.w (span f g) WalkingSpan.Hom.fst]
    exact h
  | some i =>
    cases i
    · exact Or.inl ⟨x, h⟩
    · exact Or.inr ⟨x, h⟩


section GluingLemmas
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace OpenNormalizationGluing
variable {W U V N : Scheme.{u}}
variable (f : W ⟶ U) (g : W ⟶ V) (a : W ⟶ N)
variable [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion a]
noncomputable abbrev glued : Scheme.{u} := pushout f g
noncomputable abbrev normalized : Scheme.{u} := pushout a g
noncomputable def normalizationMap (n : N ⟶ U) (h : a ≫ n = f) :
    normalized g a ⟶ glued f g :=
  pushout.desc (n ≫ pushout.inl f g) (pushout.inr f g)
    (by simp only [← Category.assoc, h]; exact pushout.condition)
@[reassoc (attr := simp)] theorem affine_chart (n : N ⟶ U) (h : a ≫ n = f) :
    pushout.inl a g ≫ normalizationMap f g a n h = n ≫ pushout.inl f g := by
  apply pushout.inl_desc
@[reassoc (attr := simp)] theorem infinity_chart (n : N ⟶ U) (h : a ≫ n = f) :
    pushout.inr a g ≫ normalizationMap f g a n h = pushout.inr f g := by
  apply pushout.inr_desc

theorem cover (z : glued f g) :
    (∃ x, pushout.inl f g x = z) ∨ ∃ y, pushout.inr f g y = z :=
  openPushout_covered f g z

theorem left_eq_right_iff (x : U) (y : V) :
    pushout.inl f g x = pushout.inr f g y ↔ ∃ w, f w = x ∧ g w = y := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, hw, hw'⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (span f g)).mp h
    cases k with
    | none =>
      have hfi : fi = WalkingSpan.Hom.fst := Subsingleton.elim _ _
      have hfj : fj = WalkingSpan.Hom.snd := Subsingleton.elim _ _
      subst fi
      subst fj
      exact ⟨w, hw, hw'⟩
    | some i =>
      cases i
      · cases fj
      · cases fi
  · rintro ⟨w, rfl, rfl⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pushout.condition]

theorem normalization_fibre (n : N ⟶ U) (h : a ≫ n = f)
    (p : U) (hp : ∀ w, f w ≠ p) (z : normalized g a) :
    normalizationMap f g a n h z = pushout.inl f g p ↔
      ∃ x, n x = p ∧ pushout.inl a g x = z := by
  constructor
  · intro hz
    rcases cover a g z with ⟨x, rfl⟩ | ⟨y, rfl⟩
    · refine ⟨x, ?_, rfl⟩
      apply (pushout.inl f g).isOpenEmbedding.injective
      simpa only [← Scheme.Hom.comp_apply, affine_chart] using hz
    · have he : pushout.inl f g p = pushout.inr f g y := by
        symm
        simpa only [← Scheme.Hom.comp_apply, infinity_chart] using hz
      obtain ⟨w, hw, -⟩ := (left_eq_right_iff f g p y).mp he
      exact (hp w hw).elim
  · rintro ⟨x, hx, rfl⟩
    rw [← Scheme.Hom.comp_apply, affine_chart, Scheme.Hom.comp_apply, hx]

theorem normalizationMap_surjective (n : N ⟶ U) (h : a ≫ n = f)
    (hn : Function.Surjective n) : Function.Surjective (normalizationMap f g a n h) := by
  intro z
  rcases cover f g z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨x, rfl⟩ := hn x
    refine ⟨pushout.inl a g x, ?_⟩
    simp only [← Scheme.Hom.comp_apply, affine_chart]
  · refine ⟨pushout.inr a g y, ?_⟩
    simp only [← Scheme.Hom.comp_apply, infinity_chart]

theorem proper_of_surjective_proper_source {P Q S : Scheme.{u}} (n : P ⟶ Q) (q : Q ⟶ S)
    [Surjective n] [IsProper (n ≫ q)] [IsSeparated q] [LocallyOfFiniteType q] : IsProper q := by
  have : UniversallyClosed q := UniversallyClosed.of_comp_surjective n q
  exact ⟨⟩

theorem preimage_affine (n : N ⟶ U) (h : a ≫ n = f) :
    normalizationMap f g a n h ⁻¹ᵁ (pushout.inl f g).opensRange =
      (pushout.inl a g).opensRange := by
  ext z
  change (∃ x, pushout.inl f g x = normalizationMap f g a n h z) ↔
    ∃ x, pushout.inl a g x = z
  constructor
  · rintro ⟨x, hx⟩
    rcases cover a g z with ⟨x', rfl⟩ | ⟨y, rfl⟩
    · exact ⟨x', rfl⟩
    · have he : pushout.inl f g x = pushout.inr f g y := by
        simpa only [← Scheme.Hom.comp_apply, infinity_chart] using hx
      obtain ⟨w, -, rfl⟩ := (left_eq_right_iff f g x y).mp he
      refine ⟨a w, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pushout.condition]
  · rintro ⟨x, rfl⟩
    refine ⟨n x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, affine_chart]

theorem preimage_infinity (n : N ⟶ U) (h : a ≫ n = f)
    (hpre : n ⁻¹ᵁ f.opensRange = a.opensRange) :
    normalizationMap f g a n h ⁻¹ᵁ (pushout.inr f g).opensRange =
      (pushout.inr a g).opensRange := by
  ext z
  change (∃ y, pushout.inr f g y = normalizationMap f g a n h z) ↔
    ∃ y, pushout.inr a g y = z
  constructor
  · rintro ⟨y, hy⟩
    rcases cover a g z with ⟨x, rfl⟩ | ⟨y', rfl⟩
    · have he : pushout.inl f g (n x) = pushout.inr f g y := by
        symm
        simpa only [← Scheme.Hom.comp_apply, affine_chart] using hy
      obtain ⟨w, hw, -⟩ := (left_eq_right_iff f g (n x) y).mp he
      have hax : x ∈ a.opensRange := by
        rw [← hpre]
        exact ⟨w, hw⟩
      obtain ⟨w', rfl⟩ := hax
      refine ⟨g w', ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pushout.condition]
    · exact ⟨y', rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    rw [← Scheme.Hom.comp_apply, infinity_chart]

theorem affine_isPullback (n : N ⟶ U) (h : a ≫ n = f) :
    IsPullback n (pushout.inl a g) (pushout.inl f g) (normalizationMap f g a n h) :=
  IsOpenImmersion.isPullback n _ _ _ (affine_chart f g a n h) (preimage_affine f g a n h)

theorem infinity_isPullback (n : N ⟶ U) (h : a ≫ n = f)
    (hpre : n ⁻¹ᵁ f.opensRange = a.opensRange) :
    IsPullback (𝟙 V) (pushout.inr a g) (pushout.inr f g) (normalizationMap f g a n h) :=
  IsOpenImmersion.isPullback (𝟙 V) _ _ _ (by simp) (preimage_infinity f g a n h hpre)

noncomputable def twoChartCover : (glued f g).OpenCover where
  I₀ := Bool
  X := fun b => if b then V else U
  f := fun b => by
    cases b
    · exact pushout.inl f g
    · exact pushout.inr f g
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro z
      rcases cover f g z with ⟨x, hx⟩ | ⟨y, hy⟩
      · exact ⟨false, x, hx⟩
      · exact ⟨true, y, hy⟩
    · intro b
      cases b <;> infer_instance

theorem normalizationMap_finite (n : N ⟶ U) (h : a ≫ n = f)
    (hpre : n ⁻¹ᵁ f.opensRange = a.opensRange) [IsFinite n] :
    IsFinite (normalizationMap f g a n h) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @AlgebraicGeometry.IsFinite) (twoChartCover f g)
  intro b
  cases b
  · change IsFinite (pullback.snd (normalizationMap f g a n h) (pushout.inl f g))
    rw [← (affine_isPullback f g a n h).flip.isoPullback_inv_snd]
    infer_instance
  · change IsFinite (pullback.snd (normalizationMap f g a n h) (pushout.inr f g))
    rw [← (infinity_isPullback f g a n h hpre).flip.isoPullback_inv_snd]
    infer_instance

end OpenNormalizationGluing
end GluingLemmas

namespace SeparatedGluing

theorem separated_of_cover {X S : Scheme.{u}} (p : X ⟶ S) (𝒰 : X.OpenCover)
    (h : ∀ i j, IsClosedImmersion (pullback.mapDesc (𝒰.f i) (𝒰.f j) p)) :
    IsSeparated p := by
  constructor
  apply IsZariskiLocalAtTarget.of_openCover
    (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒰 p p)
  intro ⟨i, j⟩
  dsimp [Scheme.Cover.pullbackHom]
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (f := (pullbackDiagonalMapIdIso ..).inv) _).mp ?_
  convert h i j using 1
  apply pullback.hom_ext <;> simp [pullback.mapDesc]

theorem closed_self {U X S : Scheme.{u}} (i : U ⟶ X) (p : X ⟶ S)
    [Mono i] [IsSeparated (i ≫ p)] : IsClosedImmersion (pullback.mapDesc i i p) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (pullback.diagonal i)]
  have he : pullback.diagonal i ≫ pullback.mapDesc i i p = pullback.diagonal (i ≫ p) := by
    apply pullback.hom_ext <;> simp [pullback.mapDesc]
  rw [he]
  infer_instance

theorem closed_symmetry {U V X S : Scheme.{u}} (i : U ⟶ X) (j : V ⟶ X) (p : X ⟶ S)
    [IsClosedImmersion (pullback.mapDesc i j p)] :
    IsClosedImmersion (pullback.mapDesc j i p) := by
  have he : pullback.mapDesc j i p =
      (pullbackSymmetry j i).hom ≫ pullback.mapDesc i j p ≫
        (pullbackSymmetry (i ≫ p) (j ≫ p)).hom := by
    apply pullback.hom_ext <;> simp [pullback.mapDesc]
  rw [he]
  infer_instance

theorem closed_overlap {W U V X S : Scheme.{u}}
    (f : W ⟶ U) (g : W ⟶ V) (i : U ⟶ X) (j : V ⟶ X) (p : X ⟶ S)
    (H : IsPullback f g i j)
    [IsClosedImmersion (pullback.lift f g (by rw [← Category.assoc, H.w, Category.assoc] :
      f ≫ (i ≫ p) = g ≫ (j ≫ p)))] : IsClosedImmersion (pullback.mapDesc i j p) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) H.isoPullback.hom]
  have he : H.isoPullback.hom ≫ pullback.mapDesc i j p =
      pullback.lift f g (by rw [← Category.assoc, H.w, Category.assoc] :
        f ≫ (i ≫ p) = g ≫ (j ≫ p)) := by
    apply pullback.hom_ext <;> simp [pullback.mapDesc]
  rw [he]
  infer_instance


theorem openPushout_isPullback {W U V : Scheme.{u}} (f : W ⟶ U) (g : W ⟶ V)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    IsPullback f g (pushout.inl f g) (pushout.inr f g) := by
  apply IsOpenImmersion.isPullback f g (pushout.inl f g) (pushout.inr f g)
    (pushout.condition.symm)
  ext y
  change (∃ x, pushout.inl f g x = pushout.inr f g y) ↔ ∃ w, g w = y
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨w, -, hy⟩ := (OpenNormalizationGluing.left_eq_right_iff f g x y).mp hx
    exact ⟨w, hy⟩
  · rintro ⟨w, rfl⟩
    exact ⟨f w, (OpenNormalizationGluing.left_eq_right_iff f g (f w) (g w)).mpr
      ⟨w, rfl, rfl⟩⟩

theorem separated_openPushout {W U V S : Scheme.{u}} (f : W ⟶ U) (g : W ⟶ V)
    [IsOpenImmersion f] [IsOpenImmersion g] (p : pushout f g ⟶ S)
    [IsSeparated (pushout.inl f g ≫ p)] [IsSeparated (pushout.inr f g ≫ p)]
    [IsClosedImmersion (pullback.lift f g (by
      rw [← Category.assoc, pushout.condition, Category.assoc] :
      f ≫ (pushout.inl f g ≫ p) = g ≫ (pushout.inr f g ≫ p)))] : IsSeparated p := by
  apply separated_of_cover p (OpenNormalizationGluing.twoChartCover f g)
  intro i j
  cases i <;> cases j
  · exact closed_self (pushout.inl f g) p
  · exact closed_overlap f g (pushout.inl f g) (pushout.inr f g) p (openPushout_isPullback f g)
  · let : IsClosedImmersion (pullback.mapDesc (pushout.inl f g) (pushout.inr f g) p) :=
      closed_overlap f g (pushout.inl f g) (pushout.inr f g) p (openPushout_isPullback f g)
    exact closed_symmetry (pushout.inl f g) (pushout.inr f g) p
  · exact closed_self (pushout.inr f g) p

theorem separated_desc {W U V S : Scheme.{u}} (f : W ⟶ U) (g : W ⟶ V)
    [IsOpenImmersion f] [IsOpenImmersion g] (pU : U ⟶ S) (pV : V ⟶ S)
    (hc : f ≫ pU = g ≫ pV) [IsSeparated pU] [IsSeparated pV]
    [IsClosedImmersion (pullback.lift f g hc)] :
    IsSeparated (pushout.desc pU pV hc) := by
  let p := pushout.desc pU pV hc
  have hU : pushout.inl f g ≫ p = pU := pushout.inl_desc _ _ _
  have hV : pushout.inr f g ≫ p = pV := pushout.inr_desc _ _ _
  let : IsSeparated (pushout.inl f g ≫ p) := hU.symm ▸ inferInstance
  let : IsSeparated (pushout.inr f g ≫ p) := hV.symm ▸ inferInstance
  let e := pullback.congrHom hU hV
  let H : f ≫ (pushout.inl f g ≫ p) = g ≫ (pushout.inr f g ≫ p) := by
    rw [hU, hV, hc]
  let : IsClosedImmersion (pullback.lift f g H) := by
    rw [← MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ e.hom]
    have he : pullback.lift f g H ≫ e.hom = pullback.lift f g hc := by
      apply pullback.hom_ext <;> simp [e]
    rw [he]
    infer_instance
  exact separated_openPushout f g p

end SeparatedGluing

theorem openPushout_compactSpace {W U V : Scheme.{u}} (f : W ⟶ U) (g : W ⟶ V)
    [IsOpenImmersion f] [IsOpenImmersion g] [CompactSpace U] [CompactSpace V] :
    CompactSpace (pushout f g : Scheme.{u}) := by
  constructor
  have hu := isCompact_range (pushout.inl f g).continuous
  have hv := isCompact_range (pushout.inr f g).continuous
  have he : Set.range (pushout.inl f g) ∪ Set.range (pushout.inr f g) = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    exact openPushout_covered f g z
  simpa only [he] using hu.union hv

end AlgebraicGeometry.Scheme
