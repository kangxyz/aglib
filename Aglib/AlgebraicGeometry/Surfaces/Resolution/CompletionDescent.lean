/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain
public import Aglib.AlgebraicGeometry.Descent.CompletionPointBlowup
public import Aglib.AlgebraicGeometry.Properties.Regular.Descent.FlatLocal
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine

/-!
# Descent of a prescribed finite normalized point-blowup chain

The original completion is a normal domain. At every specified upper centre,
the actual point square and ordinary blowup comparison give a genuine model
to which the finite-normalization/completion theorem applies. The induction
derives properness, retains the prescribed length and both projections, and
descends the supplied terminal regularity along the actual flat local maps.

The complete-local resolving chain itself is an input. This module does not
supply complete-local existence or global spreading.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Blowup

@[reassoc]
private theorem pullback_congr_first_hom_snd
    {X Y S : Scheme.{u}} {f g : X ⟶ S} (c : Y ⟶ S) (h : f = g) :
    (pullback.congrHom h rfl).hom ≫ pullback.snd g c = pullback.snd f c := by
  simp only [pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id]

@[reassoc]
private theorem pullback_congr_first_hom_fst
    {X Y S : Scheme.{u}} {f g : X ⟶ S} (c : Y ⟶ S) (h : f = g) :
    (pullback.congrHom h rfl).hom ≫ pullback.fst g c = pullback.fst f c := by
  simp only [pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id]

private theorem regularStalks_of_flat_surjective
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (β : Y ⟶ X) [Flat β] [Surjective β] (hY : RegularStalks Y) :
    RegularStalks X := by
  intro x
  obtain ⟨y, rfl⟩ := β.surjective x
  exact RegularityDescent.regular_at_image
    RegularityDescent.flatLocalRegularityDescent β y (hY y)

/-- Descend a prescribed chain from an actual proper birational integral model.
Each step uses the finite normalization comparison for that original model;
the output retains length and both projection equations. -/
theorem descend_normalizedChain_from_model
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    (hd : ringKrullDim A = 2)
    {Y Z : Scheme.{u}} {g : Z ⟶ Y} (upper : NormalizedPointBlowupChain g) :
    ∀ (X : Scheme.{u}) [IsIntegral X] (f : X ⟶ Spec (.of A))
      [IsProper f] [IsDominant f]
      (_hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
      (e : Y ≅ pullback f (Scheme.LocalRing.completionSpecMap A))
      (_hY : NormalStalks Y),
      ∃ (T : Scheme.{u}) (h : T ⟶ X) (lower : NormalizedPointBlowupChain h),
        IsProper h ∧ lower.length = upper.length ∧
          ∃ E : Z ≅ pullback (h ≫ f) (Scheme.LocalRing.completionSpecMap A),
            E.hom ≫ pullback.snd (h ≫ f) (Scheme.LocalRing.completionSpecMap A) =
              g ≫ e.hom ≫ pullback.snd f (Scheme.LocalRing.completionSpecMap A) ∧
            E.hom ≫ pullback.fst (h ≫ f) (Scheme.LocalRing.completionSpecMap A) ≫ h =
              g ≫ e.hom ≫ pullback.fst f (Scheme.LocalRing.completionSpecMap A) := by
  induction upper with
  | refl Y =>
    intro X hX f hf hdom hff e hY
    let c := Scheme.LocalRing.completionSpecMap A
    let E := e ≪≫ pullback.congrHom (Category.id_comp f).symm rfl
    refine ⟨X, 𝟙 X, .refl X, inferInstance, rfl, E, ?_, ?_⟩
    · change (e.hom ≫ (pullback.congrHom (Category.id_comp f).symm rfl).hom) ≫
        pullback.snd ((𝟙 X) ≫ f) c = (𝟙 Y) ≫ e.hom ≫ pullback.snd f c
      rw [Category.assoc, pullback_congr_first_hom_snd, Category.id_comp]
    · change (e.hom ≫ (pullback.congrHom (Category.id_comp f).symm rfl).hom) ≫
        pullback.fst ((𝟙 X) ≫ f) c ≫ 𝟙 X = (𝟙 Y) ≫ e.hom ≫ pullback.fst f c
      rw [Category.assoc, pullback_congr_first_hom_fst_assoc,
        Category.comp_id, Category.id_comp]
  | @cons Y Z hYint y hy hyne g tail ih =>
    intro X hX f hf hdom hff e hY
    let := hX
    let := hf
    let := hdom
    let := hff
    let c := Scheme.LocalRing.completionSpecMap A
    let π := e.hom ≫ pullback.fst f c
    let x := π y
    obtain ⟨hx, hxne, hI, hfinite, e₁, he₁base, he₁model⟩ :=
      exists_normalizedPointCompletion f hd hff e hY y hy hyne
    let BX := blowupDatum (X.fromSpecResidueField x).ker
    let BY := blowupDatum (Y.fromSpecResidueField y).ker
    let : IsIntegral BX.Y := pointBlowup_isIntegral X x hx hxne
    let : IsIntegral BY.Y := pointBlowup_isIntegral Y y hy hyne
    let νX := (BX.Y.fromSpecStalk (genericPoint BX.Y)).fromNormalization
    let νY := (BY.Y.fromSpecStalk (genericPoint BY.Y)).fromNormalization
    let X₁ := normalizedPointBlowup X x hx hxne
    let Y₁ := normalizedPointBlowup Y y hy hyne
    let sX : X₁ ⟶ X := normalizedPointBlowupMap X x hx hxne
    let sY : Y₁ ⟶ Y := normalizedPointBlowupMap Y y hy hyne
    let f₁ := sX ≫ f
    let hX₁ : IsIntegral X₁ := normalizedPointBlowup_isIntegral X x hx hxne
    let : IsIntegral X₁ := hX₁
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    let : IsProper BX.map := BX.isProper_of_isLocallyNoetherian
    let : IsFinite νX := hfinite
    let hsX : IsProper sX := by
      change IsProper (νX ≫ BX.map)
      infer_instance
    let : IsProper sX := hsX
    let hf₁ : IsProper f₁ := inferInstance
    let : IsProper f₁ := hf₁
    let hsXdom : IsDominant sX := normalizedPointBlowupMap_isDominant X x hx hxne
    let : IsDominant sX := hsXdom
    let hdom₁ : IsDominant f₁ := inferInstance
    let : IsDominant f₁ := hdom₁
    let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap sX)) :=
      normalizedPointBlowupMap_functionFieldMap_isIso X x hx hxne
    have hff₁ : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f₁)) := by
      change IsIso (CommRingCat.ofHom (Scheme.functionFieldMap (sX ≫ f)))
      rw [Scheme.functionFieldMap_comp, CommRingCat.ofHom_comp]
      infer_instance
    have hfirst : νX ≫ BX.map ≫ f = f₁ := (Category.assoc _ _ _).symm
    let E₁ : Y₁ ≅ pullback f₁ c := e₁ ≪≫ pullback.congrHom hfirst rfl
    have hE₁base : E₁.hom ≫ pullback.snd f₁ c = sY ≫ e.hom ≫ pullback.snd f c := by
      change (e₁.hom ≫ (pullback.congrHom hfirst rfl).hom) ≫
        pullback.snd f₁ c = sY ≫ e.hom ≫ pullback.snd f c
      rw [Category.assoc, pullback_congr_first_hom_snd]
      simpa only [sY, normalizedPointBlowupMap, Category.assoc] using he₁base
    have hrawModel : e₁.hom ≫ pullback.fst (νX ≫ BX.map ≫ f) c ≫ sX =
        sY ≫ π := by
      have hmodel : e₁.hom ≫ pullback.fst (νX ≫ BX.map ≫ f) c ≫ νX =
          νY ≫ BaseChange.map π hI BX BY := he₁model
      have h := congrArg (fun k : Y₁ ⟶ BX.Y => k ≫ BX.map) hmodel
      change e₁.hom ≫ pullback.fst (νX ≫ BX.map ≫ f) c ≫ (νX ≫ BX.map) =
        (νY ≫ BY.map) ≫ π
      simpa only [Category.assoc, BaseChange.map_triangle] using h
    have hE₁model : E₁.hom ≫ pullback.fst f₁ c ≫ sX = sY ≫ π := by
      change (e₁.hom ≫ (pullback.congrHom hfirst rfl).hom) ≫
        pullback.fst f₁ c ≫ sX = sY ≫ π
      rw [Category.assoc, pullback_congr_first_hom_fst_assoc]
      exact hrawModel
    have hY₁ : NormalStalks Y₁ := normalizedPointBlowup_normalStalks Y y hy hyne
    obtain ⟨T, h, lower, hh, hlength, E, hEbase, hEmodel⟩ :=
      ih X₁ f₁ hff₁ E₁ hY₁
    let : IsProper h := hh
    have hlast : h ≫ f₁ = (h ≫ sX) ≫ f := (Category.assoc _ _ _).symm
    let E' := E ≪≫ pullback.congrHom hlast rfl
    refine ⟨T, h ≫ sX, .cons x hx hxne h lower, inferInstance, ?_, E', ?_, ?_⟩
    · simp only [NormalizedPointBlowupChain.length, hlength]
    · change (E.hom ≫ (pullback.congrHom hlast rfl).hom) ≫
        pullback.snd ((h ≫ sX) ≫ f) c = (g ≫ sY) ≫ e.hom ≫ pullback.snd f c
      rw [Category.assoc, pullback_congr_first_hom_snd, hEbase, hE₁base]
      simp only [Category.assoc]
    · change (E.hom ≫ (pullback.congrHom hlast rfl).hom) ≫
        pullback.fst ((h ≫ sX) ≫ f) c ≫ (h ≫ sX) =
          (g ≫ sY) ≫ e.hom ≫ pullback.fst f c
      rw [Category.assoc, pullback_congr_first_hom_fst_assoc]
      calc
        E.hom ≫ pullback.fst (h ≫ f₁) c ≫ (h ≫ sX) =
            g ≫ E₁.hom ≫ pullback.fst f₁ c ≫ sX := by
          simpa only [Category.assoc] using
            congrArg (fun k : Z ⟶ X₁ => k ≫ sX) hEmodel
        _ = (g ≫ sY) ≫ e.hom ≫ pullback.fst f c := by
          rw [hE₁model]
          simp only [π, Category.assoc]

/-- Any supplied finite normalized point chain over the literal normal
completion descends with its length and original structural maps. No
regularity of its terminal scheme or existence of a resolving chain is assumed. -/
theorem exists_completionDescent_chain
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    [IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    (hd : ringKrullDim A = 2)
    {Y : Scheme.{u}}
    {g : Y ⟶ Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (upper : NormalizedPointBlowupChain g) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
      (lower : NormalizedPointBlowupChain f) (hX : IsIntegral X) (hdom : IsDominant f),
      letI := hX
      letI := hdom
      lower.length = upper.length ∧ IsProper f ∧
        IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)) ∧
        ∃ E : Y ≅ pullback f (Scheme.LocalRing.completionSpecMap A),
          E.hom ≫ pullback.snd f (Scheme.LocalRing.completionSpecMap A) = g ∧
          E.hom ≫ pullback.fst f (Scheme.LocalRing.completionSpecMap A) ≫ f =
            g ≫ Scheme.LocalRing.completionSpecMap A := by
  let H := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let c := Scheme.LocalRing.completionSpecMap A
  have hHnormal : NormalStalks (Spec (.of H)) := by
    intro x
    exact (isIntegrallyClosed_and_isDomain_stalk_Spec H x).symm
  let E₀ : Spec (.of H) ≅ pullback (𝟙 (Spec (.of A))) c :=
    (asIso (pullback.snd (𝟙 (Spec (.of A))) c)).symm
  have hE₀ : E₀.hom ≫ pullback.snd (𝟙 (Spec (.of A))) c = 𝟙 _ :=
    (asIso (pullback.snd (𝟙 (Spec (.of A))) c)).inv_hom_id
  have hff₀ : IsIso (CommRingCat.ofHom
      (Scheme.functionFieldMap (𝟙 (Spec (.of A))))) :=
    Scheme.FunctionField.fieldMap_isIso (𝟙 (Spec (.of A)))
  obtain ⟨X, f, lower, hf, hlength, E, hEbase, hEmodel⟩ :=
    descend_normalizedChain_from_model hd upper (Spec (.of A))
      (𝟙 (Spec (.of A))) hff₀ E₀ hHnormal
  let : IsProper f := hf
  let hX : IsIntegral X := lower.isIntegral inferInstance
  let : IsIntegral X := hX
  let hdom : IsDominant f := lower.isDominant inferInstance
  let : IsDominant f := hdom
  let E' : Y ≅ pullback f c := E ≪≫ pullback.congrHom (Category.comp_id f) rfl
  have hbase : E'.hom ≫ pullback.snd f c = g := by
    change (E.hom ≫ (pullback.congrHom (Category.comp_id f) rfl).hom) ≫
      pullback.snd f c = g
    rw [Category.assoc, pullback_congr_first_hom_snd, hEbase, hE₀, Category.comp_id]
  have hmodel : E'.hom ≫ pullback.fst f c ≫ f = g ≫ c := by
    rw [pullback.condition, ← Category.assoc, hbase]
  have hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)) :=
    lower.functionFieldMap_isIso inferInstance
  exact ⟨X, f, lower, hX, hdom, hlength, hf, hff, E', hbase, hmodel⟩

/-- A supplied finite normalized closed-point blowup chain over the NORMAL
literal completion descends, with the same length and original structural
maps. Its supplied terminal regularity descends along the actual flat local
stalk maps. No complete-local resolving-chain existence is asserted. -/
theorem exists_completionDescent
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    [IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    (hd : ringKrullDim A = 2)
    {Y : Scheme.{u}}
    {g : Y ⟶ Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (upper : NormalizedPointBlowupChain g) (hY : RegularStalks Y) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
      (lower : NormalizedPointBlowupChain f) (hX : IsIntegral X) (hdom : IsDominant f),
      letI := hX
      letI := hdom
      lower.length = upper.length ∧ IsProper f ∧
        IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)) ∧ RegularStalks X ∧
        ∃ E : Y ≅ pullback f (Scheme.LocalRing.completionSpecMap A),
          E.hom ≫ pullback.snd f (Scheme.LocalRing.completionSpecMap A) = g ∧
          E.hom ≫ pullback.fst f (Scheme.LocalRing.completionSpecMap A) ≫ f =
            g ≫ Scheme.LocalRing.completionSpecMap A := by
  obtain ⟨X, f, lower, hX, hdom, hlength, hf, hff, E', hbase, hmodel⟩ :=
    exists_completionDescent_chain A hd upper
  let : IsIntegral X := hX
  let : IsDominant f := hdom
  let : IsProper f := hf
  let H := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let c := Scheme.LocalRing.completionSpecMap A
  let Xhat : Scheme.{u} := pullback f c
  let β : Xhat ⟶ X := pullback.fst f c
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherianRing H := AdicCompletion.isNoetherianRing A (IsLocalRing.maximalIdeal A)
  let : IsLocallyNoetherian Xhat :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f c)
  let : Flat c := (CompletionNormalization.completion_flat_surjective A).1
  let : Surjective c := (CompletionNormalization.completion_flat_surjective A).2
  let : Flat β := MorphismProperty.of_isPullback
    (P := @Flat) (IsPullback.of_hasPullback f c).flip inferInstance
  let : Surjective β := inferInstance
  have hhat : RegularStalks Xhat := hY.of_isOpenImmersion E'.inv
  have hregular : RegularStalks X := regularStalks_of_flat_surjective β hhat
  have hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)) :=
    lower.functionFieldMap_isIso inferInstance
  exact ⟨X, f, lower, hX, hdom, hlength, hf, hff, hregular, E', hbase, hmodel⟩

end AlgebraicGeometry.Scheme.Blowup
