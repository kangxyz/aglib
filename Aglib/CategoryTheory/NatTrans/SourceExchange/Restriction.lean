/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.OpenComparisonPasting
public import Aglib.CategoryTheory.NatTrans.CompositeExchange
public import Aglib.CategoryTheory.NatTrans.CompositeExchangeRestriction
public import Aglib.CategoryTheory.NatTrans.NormalizedExchangeNaturality
public import Aglib.CategoryTheory.NatTrans.SourceExchange.Pasting
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uA' uE uP uP' uB uA₁ uA₂ uE' uP₁ uP₂ vA vA' vE vP vP' vB vA₁ vA₂ vE' vP₁ vP₂

section Algebra
variable {A : Type uA} {A' : Type uA'} {E : Type uE} {P : Type uP} {P' : Type uP'}
  [Category.{vA} A] [Category.{vA'} A'] [Category.{vE} E] [Category.{vP} P] [Category.{vP'} P']
  {F : A ⥤ E} {F' : A' ⥤ E} {V : A ⥤ A'} {IE : E ⥤ E}
  {K : P ⥤ A} {K' : P' ⥤ A'} {W : P ⥤ P'}

/-- Restrict a specified original source-transport isomorphism. -/
def restrictSourceIso (s : F ≅ V ⋙ F') (e : K ⋙ V ≅ W ⋙ K') :
    K ⋙ F ≅ W ⋙ (K' ⋙ F') :=
  Functor.isoWhiskerLeft K s ≪≫ (Functor.associator K V F').symm ≪≫
    Functor.isoWhiskerRight e F' ≪≫ Functor.associator W K' F'

/-- Whole defining-formula boundary for the original source restriction. -/
def SourceIsoRestrictionEquation
    (sr : K ⋙ F ≅ W ⋙ (K' ⋙ F')) (s : F ≅ V ⋙ F')
    (e : K ⋙ V ≅ W ⋙ K') : Prop := sr = restrictSourceIso s e

/-- Original exchange normalization survives native source restriction. -/
theorem sourceIsoExchange_restrict
    (β : F ⋙ IE ⟶ V ⋙ F') (i : IE ≅ 𝟭 E) (s : F ≅ V ⋙ F')
    (e : K ⋙ V ≅ W ⋙ K') (sr : K ⋙ F ≅ W ⋙ (K' ⋙ F'))
    (hsr : SourceIsoRestrictionEquation sr s e)
    (hβ : SourceIsoExchangeEquation β i s) :
    SourceIsoExchangeEquation (compositeExchange β e) i sr := by
  change sr = restrictSourceIso s e at hsr
  subst sr
  intro x
  have h := congrArg (fun z => z ≫ F'.map (e.hom.app x)) (hβ (K.obj x))
  simpa only [compositeExchange_app, restrictSourceIso, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.comp_obj, Category.id_comp, Category.comp_id,
    Category.assoc] using h

variable {B : Type uB} [Category.{vB} B] {J : A ⥤ B} {J' : A' ⥤ B} {R : B ⥤ E}

/-- The two original open/proper factors have precisely the canonical restricted
whole formula, before any concrete derived models are substituted. -/
theorem sourceIsoRestrictionEquation_factors
    (s₀ : J ≅ V ⋙ J') (e : K ⋙ V ≅ W ⋙ K') :
    SourceIsoRestrictionEquation
      (Functor.isoWhiskerLeft K (Functor.isoWhiskerRight s₀ R) ≪≫
        Functor.isoWhiskerLeft K (Functor.associator V J' R) ≪≫
        (Functor.associator K V (J' ⋙ R)).symm ≪≫
        Functor.isoWhiskerRight e (J' ⋙ R) ≪≫ Functor.associator W K' (J' ⋙ R))
      (Functor.isoWhiskerRight s₀ R ≪≫ Functor.associator V J' R) e := by
  simp only [SourceIsoRestrictionEquation, restrictSourceIso, Functor.isoWhiskerLeft_trans,
    Iso.trans_assoc]
end Algebra

theorem sourceIsoNaturality_restrict
    {A : Type uA} {A' : Type uA'} {E : Type uE} {P : Type uP} {P' : Type uP'} [Category.{vA} A]
    [Category.{vA'} A'] [Category.{vE} E]
    [Category.{vP} P] [Category.{vP'} P']
    {F₁ F₂ : A ⥤ E} {F₁' F₂' : A' ⥤ E} {V : A ⥤ A'}
    {K : P ⥤ A} {K' : P' ⥤ A'} {W : P ⥤ P'}
    (t : F₂ ⟶ F₁) (t' : F₂' ⟶ F₁')
    (s₁ : F₁ ≅ V ⋙ F₁') (s₂ : F₂ ≅ V ⋙ F₂') (e : K ⋙ V ≅ W ⋙ K')
    (sr₁ : K ⋙ F₁ ≅ W ⋙ (K' ⋙ F₁')) (sr₂ : K ⋙ F₂ ≅ W ⋙ (K' ⋙ F₂'))
    (h₁ : SourceIsoRestrictionEquation sr₁ s₁ e)
    (h₂ : SourceIsoRestrictionEquation sr₂ s₂ e)
    (h : SourceIsoNaturalityEquation t t' s₁ s₂) :
    SourceIsoNaturalityEquation (Functor.whiskerLeft K t) (Functor.whiskerLeft K' t')
      sr₁ sr₂ := by
  change sr₁ = restrictSourceIso s₁ e at h₁
  change sr₂ = restrictSourceIso s₂ e at h₂
  subst sr₁ sr₂
  apply NatTrans.ext
  funext x
  have hx := congrArg (fun z => z.app (K.obj x)) h
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hx
  simp only [restrictSourceIso, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.comp_obj, Category.id_comp, Category.comp_id, Category.assoc]
  rw [← Category.assoc, hx, Category.assoc]
  exact congrArg (fun z => s₂.hom.app (K.obj x) ≫ z) (t'.naturality (e.hom.app x)).symm

theorem sourceIsoPasting_restrict
    {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {E : Type uE} {E' : Type uE'} {P : Type uP}
    {P₁ : Type uP₁} {P₂ : Type uP₂}
    [Category.{vA} A] [Category.{vA₁} A₁] [Category.{vA₂} A₂] [Category.{vE} E] [Category.{vE'} E']
    [Category.{vP} P] [Category.{vP₁} P₁] [Category.{vP₂} P₂]
    {F : A ⥤ E} {F₁ : A₁ ⥤ E'} {F₂ : A₂ ⥤ E'} {B : E ⥤ E'}
    {V₁ : A ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V : A ⥤ A₂}
    {K : P ⥤ A} {K₁ : P₁ ⥤ A₁} {K₂ : P₂ ⥤ A₂}
    {W₁ : P ⥤ P₁} {W₂ : P₁ ⥤ P₂} {W : P ⥤ P₂}
    (β : F ⋙ B ⟶ V₁ ⋙ F₁) (β' : F ⋙ B ⟶ V ⋙ F₂)
    (s : F₁ ≅ V₂ ⋙ F₂) (c : V ≅ V₁ ⋙ V₂)
    (e₁ : K ⋙ V₁ ≅ W₁ ⋙ K₁) (e₂ : K₁ ⋙ V₂ ≅ W₂ ⋙ K₂)
    (e : K ⋙ V ≅ W ⋙ K₂) (cw : W ≅ W₁ ⋙ W₂)
    (sr : K₁ ⋙ F₁ ≅ W₂ ⋙ (K₂ ⋙ F₂))
    (hs : SourceIsoRestrictionEquation sr s e₂)
    (hβ : CompactifiedSourceIsoPastingEquation β β' c s)
    (he : LeftComparisonPastingEquation e₁ e₂ e cw c) :
    CompactifiedSourceIsoPastingEquation
      (compositeExchange β e₁) (compositeExchange β' e) cw sr := by
  change sr = restrictSourceIso s e₂ at hs
  subst sr
  intro x
  simp only [compositeExchange_app, Functor.comp_map, restrictSourceIso, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.comp_obj, Category.id_comp, Category.comp_id,
    Category.assoc]
  rw [← F₂.map_comp, ← he x, F₂.map_comp, F₂.map_comp]
  rw [← Category.assoc, ← Category.assoc, hβ (K.obj x)]
  simp only [Category.assoc]
  simpa only [Functor.comp_obj, Functor.comp_map, Category.assoc] using
    (congrArg (fun z => β.app (K.obj x) ≫ z ≫ F₂.map (e₂.hom.app (W₁.obj x)))
      (s.hom.naturality (e₁.hom.app x)).symm)

theorem targetIsoBaseChange_restrict
    {P : Type uP} {A : Type uA} {E : Type uE} {P' : Type uP'} {A' : Type uA'} {E' : Type uE'}
    [Category.{vP} P] [Category.{vA} A] [Category.{vE} E]
    [Category.{vP'} P'] [Category.{vA'} A'] [Category.{vE'} E']
    {K : P ⥤ A} {K' : P' ⥤ A'} {W : P ⥤ P'} {V : A ⥤ A'}
    {F : A ⥤ E} {F₁ F₂ : A' ⥤ E'} {B : E ⥤ E'}
    (β₁ : F ⋙ B ⟶ V ⋙ F₁) (β₂ : F ⋙ B ⟶ V ⋙ F₂)
    (t : F₂ ⟶ F₁) (e : K ⋙ V ≅ W ⋙ K')
    (h : TargetIsoBaseChangeEquation β₁ β₂ t) :
    TargetIsoBaseChangeEquation (compositeExchange β₁ e) (compositeExchange β₂ e)
      (Functor.whiskerLeft K' t) := by
  change β₁ = β₂ ≫ Functor.whiskerLeft V t at h
  change compositeExchange β₁ e = compositeExchange β₂ e ≫
    Functor.whiskerLeft W (Functor.whiskerLeft K' t)
  have hn : Functor.whiskerRight (𝟙 F) B ≫ β₁ = β₂ ≫ Functor.whiskerLeft V t := by
    simpa only [Functor.whiskerRight_id', Category.id_comp] using h
  have hr := compositeExchange_restriction_naturality β₁ β₂ e (𝟙 F) t hn
  simpa only [Functor.whiskerLeft_id', Functor.whiskerRight_id', Category.id_comp] using hr

theorem sourceIsoBefore_restrict
    {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {E : Type uE} {E' : Type uE'} {P : Type uP}
    {P₁ : Type uP₁} {P₂ : Type uP₂}
    [Category.{vA} A] [Category.{vA₁} A₁] [Category.{vA₂} A₂] [Category.{vE} E] [Category.{vE'} E']
    [Category.{vP} P] [Category.{vP₁} P₁] [Category.{vP₂} P₂]
    {F : A ⥤ E} {F₁ : A₁ ⥤ E} {F₂ : A₂ ⥤ E'} {B : E ⥤ E'}
    {V₁ : A ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V : A ⥤ A₂}
    {K : P ⥤ A} {K₁ : P₁ ⥤ A₁} {K₂ : P₂ ⥤ A₂}
    {W₁ : P ⥤ P₁} {W₂ : P₁ ⥤ P₂} {W : P ⥤ P₂}
    (s : F ≅ V₁ ⋙ F₁) (β₁ : F₁ ⋙ B ⟶ V₂ ⋙ F₂)
    (β : F ⋙ B ⟶ V ⋙ F₂) (c : V ≅ V₁ ⋙ V₂)
    (e₁ : K ⋙ V₁ ≅ W₁ ⋙ K₁) (e₂ : K₁ ⋙ V₂ ≅ W₂ ⋙ K₂)
    (e : K ⋙ V ≅ W ⋙ K₂) (cw : W ≅ W₁ ⋙ W₂)
    (sr : K ⋙ F ≅ W₁ ⋙ (K₁ ⋙ F₁))
    (hs : SourceIsoRestrictionEquation sr s e₁)
    (hβ : SourceIsoBeforeExchangeEquation s β₁ β c)
    (he : LeftComparisonPastingEquation e₁ e₂ e cw c) :
    SourceIsoBeforeExchangeEquation sr (compositeExchange β₁ e₂)
      (compositeExchange β e) cw := by
  change sr = restrictSourceIso s e₁ at hs
  subst sr
  intro x
  have hn := β₁.naturality (e₁.hom.app x)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [compositeExchange_app, Functor.comp_map, restrictSourceIso, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.comp_obj, Category.id_comp, Category.comp_id,
    B.map_comp, Category.assoc]
  rw [← Category.assoc (B.map (F₁.map (e₁.hom.app x))), hn]
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc, hβ (K.obj x)]
  simp only [Category.assoc]
  rw [← F₂.map_comp, ← F₂.map_comp, he x, F₂.map_comp]

end CategoryTheory
