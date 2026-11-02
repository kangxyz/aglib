/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.LocalModification.FactorNormalization
public import Aglib.AlgebraicGeometry.Descent.LocalModification.NormalizedPointLocalization
public import Aglib.AlgebraicGeometry.Descent.LocalModification.NormalizationAway
public import Aglib.AlgebraicGeometry.Blowup.Properness

/-!
# Prescribed supported normalized point chains

The induction keeps the original local-spectrum square and the proper total
terminal map. Each centre is the image of the prescribed local centre.
Finiteness of the next literal normalization is derived from a constructed
proper normal terminal factor, not imposed as a globalization certificate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.LocalModification

open Blowup

/-- Serial globalization from an actual proper intermediate model. The
specified local terminal map remains proper throughout the induction. -/
theorem globalize_normalizedChain_from_model
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : NormalStalks X) (x : X) (hx : IsClosed ({x} : Set X))
    (hxη : x ≠ genericPoint X)
    {Y T : Scheme.{u}} {g : T ⟶ Y} (upper : NormalizedPointBlowupChain g) :
    ∀ (_hY : IsIntegral Y) (_hYn : NormalStalks Y)
      (S : Scheme.{u}) [IsIntegral S] (_hS : NormalStalks S)
      (f : S ⟶ X) [IsProper f]
      (_hfU : IsIso (f ∣_ pointComplement x hx))
      (π : Y ⟶ S) (pY : Y ⟶ Spec (X.presheaf.stalk x))
      [IsProper pY] [IsDominant pY]
      (_H : IsPullback π pY f (X.fromSpecStalk x))
      [IsProper (g ≫ pY)]
      (_hpU : IsIso ((g ≫ pY) ∣_ X.fromSpecStalk x ⁻¹ᵁ pointComplement x hx)),
      ∃ (Z : Scheme.{u}) (h : Z ⟶ S) (lower : NormalizedPointBlowupChain h)
        (a : T ⟶ Z),
        IsProper h ∧ lower.length = upper.length ∧
        IsPullback a (g ≫ pY) (h ≫ f) (X.fromSpecStalk x) ∧
        a ≫ h = g ≫ π ∧ IsIso ((h ≫ f) ∣_ pointComplement x hx) := by
  induction upper with
  | refl Y =>
    intro hY hYn S hSint hS f hf hfU π pY hpY hdY H hp hpU
    refine ⟨S, 𝟙 S, .refl S, π, inferInstance, rfl, ?_, ?_, ?_⟩
    · simpa only [Category.id_comp] using H
    · simp
    · rw [Category.id_comp]
      exact hfU
  | @cons Y T hYi y hy hyη t tail ih =>
    intro hY hYn S hSint hS f hf hfU π pY hpY hdY H hp hpU
    let := hY
    let := hSint
    let := hf
    let := hpY
    let := hdY
    let c := X.fromSpecStalk x
    let U := pointComplement x hx
    let : Flat c := Scheme.fromSpecStalk_flat X x
    let : Flat π := MorphismProperty.of_isPullback H.flip inferInstance
    let : IsPreimmersion π := MorphismProperty.of_isPullback H.flip inferInstance
    let : IsDominant π := Scheme.isDominant_of_flat_of_nonempty π
    obtain ⟨hz, hzx⟩ := localizationClosedPoint_data x hx π pY f H y hy
    have hzη : π y ≠ genericPoint S := by
      intro he
      apply hyη
      apply π.injective
      exact he.trans (Scheme.map_genericPoint_of_isDominant Y π).symm
    let BX := blowupDatum (S.fromSpecResidueField (π y)).ker
    let BY := blowupDatum (Y.fromSpecResidueField y).ker
    let : IsIntegral BX.Y := pointBlowup_isIntegral S (π y) hz hzη
    let : IsIntegral BY.Y := pointBlowup_isIntegral Y y hy hyη
    let : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian f
    let : IsProper BX.map := BX.isProper_of_isLocallyNoetherian
    let νX := (BX.Y.fromSpecStalk (genericPoint BX.Y)).fromNormalization
    let νY := (BY.Y.fromSpecStalk (genericPoint BY.Y)).fromNormalization
    let Y₁ := normalizedPointBlowup Y y hy hyη
    let S₁ := normalizedPointBlowup S (π y) hz hzη
    let sY : Y₁ ⟶ Y := normalizedPointBlowupMap Y y hy hyη
    let sX : S₁ ⟶ S := normalizedPointBlowupMap S (π y) hz hzη
    let : IsIntegral Y₁ := normalizedPointBlowup_isIntegral Y y hy hyη
    let : IsIntegral S₁ := normalizedPointBlowup_isIntegral S (π y) hz hzη
    let : IsIntegral T := tail.isIntegral inferInstance
    let : IsDominant t := tail.isDominant inferInstance
    let : IsDominant sY := normalizedPointBlowupMap_isDominant Y y hy hyη
    let p := (t ≫ sY) ≫ pY
    let : IsProper p := hp
    let : IsDominant p := inferInstance
    have hT : NormalStalks T := tail.normalStalks
      (normalizedPointBlowup_normalStalks Y y hy hyη)
    let hI := pointCentre_comap_of_flat_preimmersion π y hz
    let b₀ := BaseChange.map π hI BX BY
    let a₀ : T ⟶ BX.Y := t ≫ νY ≫ b₀
    have ha₀ : a₀ ≫ (BX.map ≫ f) = p ≫ c := by
      change (t ≫ νY ≫ b₀) ≫ (BX.map ≫ f) = ((t ≫ (νY ≫ BY.map)) ≫ pY) ≫ c
      have hb₀ : b₀ ≫ BX.map = BY.map ≫ π := BaseChange.map_triangle π hI BX BY
      simp only [Category.assoc]
      rw [← Category.assoc b₀ BX.map f, hb₀, Category.assoc, H.w]
    have hBU : IsIso ((BX.map ≫ f) ∣_ U) := by
      have hBX : IsIso (BX.map ∣_ f ⁻¹ᵁ U) := by
        apply BX.restrict_isIso_of_disjoint
        rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hz.closure_eq]
        apply Set.disjoint_singleton_right.mpr
        change ¬ f (π y) ≠ x
        exact fun he => he hzx
      let := hBX
      let := hfU
      rw [morphismRestrict_comp]
      infer_instance
    let : IsFinite νX := genericNormalization_isFinite_of_stalk_factor
      hX hT x hx hxη (BX.map ≫ f) hBU p hpU a₀ ha₀
    let : IsProper sX := by
      change IsProper (νX ≫ BX.map)
      infer_instance
    let f₁ := sX ≫ f
    let : IsProper f₁ := inferInstance
    let E := normalizedPointLocalizationIso π y hy hyη hz hzη
    let β : Y₁ ⟶ S₁ := E.hom ≫ pullback.fst sX π
    have HE : IsPullback β sY sX π := by
      apply (IsPullback.of_hasPullback sX π).of_iso' E (.refl _) (.refl _) (.refl _)
      · rfl
      · exact normalizedPointLocalizationIso_hom_snd π y hy hyη hz hzη
      · simp
      · simp
    let pY₁ := sY ≫ pY
    have H₁ : IsPullback β pY₁ f₁ c := HE.paste_vert H
    let : IsProper pY₁ := MorphismProperty.of_isPullback H₁ inferInstance
    let : IsDominant pY₁ := inferInstance
    let : IsProper (t ≫ pY₁) := by
      change IsProper (t ≫ sY ≫ pY)
      rw [← Category.assoc]
      exact hp
    have hpU₁ : IsIso ((t ≫ pY₁) ∣_ c ⁻¹ᵁ U) := by
      change IsIso ((t ≫ sY ≫ pY) ∣_ c ⁻¹ᵁ U)
      rw [← Category.assoc]
      exact hpU
    let : Nonempty U := ⟨⟨genericPoint X, hxη.symm⟩⟩
    let : IsIso (f ∣_ U) := hfU
    let : Nonempty (f ⁻¹ᵁ U) := Nonempty.map (inv (f ∣_ U)) inferInstance
    have hsU : IsIso (sX ∣_ f ⁻¹ᵁ U) := by
      apply normalizedPointBlowupMap_isIso_restrict_away S hS (π y) hz hzη
      change ¬ f (π y) ≠ x
      exact fun he => he hzx
    have hfU₁ : IsIso (f₁ ∣_ U) := by
      change IsIso ((sX ≫ f) ∣_ U)
      rw [morphismRestrict_comp]
      let := hsU
      infer_instance
    obtain ⟨Z, h, lower, a, hh, hlen, Ha, haw, hU⟩ :=
      ih (normalizedPointBlowup_isIntegral Y y hy hyη)
        (normalizedPointBlowup_normalStalks Y y hy hyη)
        S₁ (normalizedPointBlowup_normalStalks S (π y) hz hzη)
        f₁ hfU₁ β pY₁ H₁ hpU₁
    let := hh
    refine ⟨Z, h ≫ sX, .cons (π y) hz hzη h lower, a, inferInstance, ?_, ?_, ?_, ?_⟩
    · simpa only [NormalizedPointBlowupChain.length] using congrArg (· + 1) hlen
    · simpa only [f₁, pY₁, Category.assoc] using Ha
    · rw [← Category.assoc, haw, Category.assoc, HE.w]
      simp only [Category.assoc]
      rfl
    · rw [Category.assoc]
      exact hU

/-- A supplied proper punctured-isomorphism local chain globalizes to an
actual chain supported at the original closed point, with exactly its length
and the original cartesian terminal comparison. -/
theorem exists_supported_normalizedChain_of_punctured
    {X T : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : NormalStalks X) (x : X) (hx : IsClosed ({x} : Set X))
    (hxη : x ≠ genericPoint X)
    (p : T ⟶ Spec (X.presheaf.stalk x)) [IsProper p]
    (upper : NormalizedPointBlowupChain p)
    (hpU : IsIso (p ∣_ X.fromSpecStalk x ⁻¹ᵁ pointComplement x hx)) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (lower : NormalizedPointBlowupChain f)
      (a : T ⟶ Z), IsProper f ∧ lower.length = upper.length ∧
      IsPullback a p f (X.fromSpecStalk x) ∧ IsIso (f ∣_ pointComplement x hx) := by
  let Y := Spec (X.presheaf.stalk x)
  let c := X.fromSpecStalk x
  have H : IsPullback c (𝟙 Y) (𝟙 X) c :=
    IsPullback.of_vert_isIso ⟨(Category.comp_id c).trans (Category.id_comp c).symm⟩
  let : IsProper (p ≫ 𝟙 Y) := by
    rw [Category.comp_id]
    infer_instance
  have hp : IsIso ((p ≫ 𝟙 Y) ∣_ c ⁻¹ᵁ pointComplement x hx) := by
    rw [Category.comp_id]
    exact hpU
  obtain ⟨Z, f, lower, a, hf, hlen, Ha, _haw, hU⟩ :=
    globalize_normalizedChain_from_model hX x hx hxη upper inferInstance
      (normalStalks_stalkSpec X hX x) X hX (𝟙 X) (by infer_instance)
      c (𝟙 Y) H hp
  refine ⟨Z, f, lower, a, hf, hlen, ?_, ?_⟩
  · rw [Category.comp_id p, Category.comp_id f] at Ha
    exact Ha
  · rw [Category.comp_id] at hU
    exact hU

end AlgebraicGeometry.Scheme.LocalModification
