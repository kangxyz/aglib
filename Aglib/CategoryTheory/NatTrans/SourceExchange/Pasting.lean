/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.Whole
public import Aglib.CategoryTheory.Adjunction.OpenComparisonPasting
public import Aglib.CategoryTheory.Functor.ImageComparison
public import Aglib.CategoryTheory.NatTrans.CompositeExchange
public import Aglib.CategoryTheory.NatTrans.CompositeExchangePasting
public import Aglib.CategoryTheory.NatTrans.ImageComparisonBaseChange
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uE uA uA₁ uA₂ uB uC uE' uA' uU uS uU' uC' uD' uT uM uN uA₀ uB₀ uC₀ uB₁ uC₁ uB₂ uC₂ vE
universe vA vA₁ vA₂ vB vC vE' vA' vU vS vU' vC' vD' vT vM vN vA₀ vB₀ vC₀ vB₁ vC₁ vB₂ vC₂

theorem source_transport_from_identity_pasting
    {E : Type uE} [Category.{vE} E] {I : E ⥤ E} (d : I ≅ 𝟭 E)
    {W X Y Z : E} (a : X ⟶ Y) (δ : I.obj Y ⟶ Z) (s : Y ⟶ Z)
    (c : W ⟶ I.obj X) (t : W ≅ X) (p : W ⟶ Z) (q : X ⟶ Z)
    (hs : s = d.inv.app Y ≫ δ) (hc : c ≫ d.hom.app X = t.hom)
    (hp : c ≫ I.map a ≫ δ = p) (ht : t.hom ≫ q = p) : q = a ≫ s := by
  apply (cancel_epi t.hom).mp
  rw [ht, ← hp, hs, ← hc]
  have hn := d.hom.naturality a
  change I.map a ≫ d.hom.app Y = d.hom.app X ≫ a at hn
  simp only [Category.assoc]
  rw [← reassoc_of% hn, Iso.hom_inv_id_app_assoc]

/-- Whole source-transport equation for the original open comparisons. -/
def OpenSourceIsoPastingEquation
    {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {B : Type uB} {C : Type uC} [Category.{vA} A]
    [Category.{vA₁} A₁] [Category.{vA₂} A₂]
    [Category.{vB} B] [Category.{vC} C]
    {J : A ⥤ B} {J₁ : A₁ ⥤ C} {J₂ : A₂ ⥤ C} {Q : B ⥤ C}
    {V₁ : A ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V : A ⥤ A₂}
    (e : J ⋙ Q ≅ V₁ ⋙ J₁) (e' : J ⋙ Q ≅ V ⋙ J₂)
    (s : J₁ ≅ V₂ ⋙ J₂) (c : V ≅ V₁ ⋙ V₂) : Prop :=
  ∀ K, e'.hom.app K ≫ J₂.map (c.hom.app K) =
    e.hom.app K ≫ s.hom.app (V₁.obj K)

/-- Whole original compactified exchange/source-transport equation. -/
def CompactifiedSourceIsoPastingEquation
    {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {E : Type uE} {E' : Type uE'} [Category.{vA} A]
    [Category.{vA₁} A₁] [Category.{vA₂} A₂]
    [Category.{vE} E] [Category.{vE'} E']
    {F : A ⥤ E} {F₁ : A₁ ⥤ E'} {F₂ : A₂ ⥤ E'} {B : E ⥤ E'}
    {V₁ : A ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V : A ⥤ A₂}
    (β : F ⋙ B ⟶ V₁ ⋙ F₁) (β' : F ⋙ B ⟶ V ⋙ F₂)
    (c : V ≅ V₁ ⋙ V₂) (s : F₁ ≅ V₂ ⋙ F₂) : Prop :=
  ∀ K, β'.app K ≫ F₂.map (c.hom.app K) = β.app K ≫ s.hom.app (V₁.obj K)

theorem compactifiedSourceIsoPasting_of_open
    {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {B : Type uB} {C : Type uC} {E : Type uE}
    {E' : Type uE'} [Category.{vA} A] [Category.{vA₁} A₁] [Category.{vA₂} A₂]
    [Category.{vB} B] [Category.{vC} C] [Category.{vE} E] [Category.{vE'} E']
    {J : A ⥤ B} {J₁ : A₁ ⥤ C} {J₂ : A₂ ⥤ C} {Q : B ⥤ C}
    {V₁ : A ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V : A ⥤ A₂}
    {R : B ⥤ E} {R' : C ⥤ E'} {F : E ⥤ E'}
    (β : R ⋙ F ⟶ Q ⋙ R') (e : J ⋙ Q ≅ V₁ ⋙ J₁) (e' : J ⋙ Q ≅ V ⋙ J₂)
    (s : J₁ ≅ V₂ ⋙ J₂) (c : V ≅ V₁ ⋙ V₂)
    (h : OpenSourceIsoPastingEquation e e' s c) :
    CompactifiedSourceIsoPastingEquation (compositeExchange β e) (compositeExchange β e') c
      (Functor.isoWhiskerRight s R' ≪≫ Functor.associator V₂ J₂ R') := by
  intro K
  simp only [compositeExchange_app, Functor.comp_map, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.comp_obj, Category.comp_id, Category.assoc]
  rw [← R'.map_comp, h K, R'.map_comp]

/-- Whole original target-model transport equation. -/
def TargetIsoBaseChangeEquation
    {A : Type uA} {A' : Type uA'} {E : Type uE} {E' : Type uE'} [Category.{vA} A]
    [Category.{vA'} A'] [Category.{vE} E] [Category.{vE'} E']
    {F : A ⥤ E} {F₁ F₂ : A' ⥤ E'} {B : E ⥤ E'} {V : A ⥤ A'}
    (β₁ : F ⋙ B ⟶ V ⋙ F₁) (β₂ : F ⋙ B ⟶ V ⋙ F₂) (t : F₂ ⟶ F₁) : Prop :=
  β₁ = β₂ ≫ Functor.whiskerLeft V t

theorem targetIsoBaseChange_of_identity_source
    {U : Type uU} {C : Type uC} {S : Type uS} {U' : Type uU'} {C' : Type uC'} {D' : Type uD'}
    {T : Type uT}
    [Category.{vU} U] [Category.{vC} C] [Category.{vS} S] [Category.{vU'} U']
    [Category.{vC'} C'] [Category.{vD'} D'] [Category.{vT} T]
    {J : U ⥤ C} {R : C ⥤ C} {P : C ⥤ S}
    {F : S ⥤ T} {V : U ⥤ U'} {Q₁ : C ⥤ C'} {Q₂ : C ⥤ D'}
    {R' : C' ⥤ D'} {P₁' : C' ⥤ T} {P₂' : D' ⥤ T}
    {J₁' : U' ⥤ C'} {J₂' : U' ⥤ D'}
    (δ : J ⟶ J ⋙ R) (δ' : J₂' ⟶ J₁' ⋙ R')
    (τ : R ⋙ P ≅ P) (τ' : R' ⋙ P₂' ≅ P₁')
    (β₁ : P ⋙ F ⟶ Q₁ ⋙ P₁') (β₂ : P ⋙ F ⟶ Q₂ ⋙ P₂')
    (e₁ : J ⋙ Q₁ ≅ V ⋙ J₁') (e₂ : J ⋙ Q₂ ≅ V ⋙ J₂')
    (hn : ImageComparisonBaseChangeEquation δ δ' τ τ' β₁ β₂ e₁ e₂)
    (hi : imageComparison δ τ = 𝟙 (J ⋙ P)) :
    TargetIsoBaseChangeEquation (compositeExchange β₁ e₁) (compositeExchange β₂ e₂)
      (imageComparison δ' τ') := by
  change Functor.whiskerRight (imageComparison δ τ) F ≫ compositeExchange β₁ e₁ = _ at hn
  rw [hi, Functor.whiskerRight_id', Category.id_comp] at hn
  exact hn

/-- Whole source-before-exchange equation with the original inverse-image compositor. -/
def SourceIsoBeforeExchangeEquation
    {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {E : Type uE} {E' : Type uE'} [Category.{vA} A]
    [Category.{vA₁} A₁] [Category.{vA₂} A₂]
    [Category.{vE} E] [Category.{vE'} E']
    {F : A ⥤ E} {F₁ : A₁ ⥤ E} {F₂ : A₂ ⥤ E'} {B : E ⥤ E'}
    {V₁ : A ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V : A ⥤ A₂}
    (s : F ≅ V₁ ⋙ F₁) (β₁ : F₁ ⋙ B ⟶ V₂ ⋙ F₂)
    (β : F ⋙ B ⟶ V ⋙ F₂) (c : V ≅ V₁ ⋙ V₂) : Prop :=
  ∀ K, B.map (s.hom.app K) ≫ β₁.app (V₁.obj K) = β.app K ≫ F₂.map (c.hom.app K)

theorem sourceIsoBeforeExchange_of_open
    {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {M : Type uM} {N : Type uN} {E : Type uE}
    {E' : Type uE'} [Category.{vA} A] [Category.{vA₁} A₁] [Category.{vA₂} A₂]
    [Category.{vM} M] [Category.{vN} N] [Category.{vE} E] [Category.{vE'} E']
    {J : A ⥤ M} {J₁ : A₁ ⥤ M} {J₂ : A₂ ⥤ N} {Q : M ⥤ N}
    {R : M ⥤ E} {R' : N ⥤ E'} {B : E ⥤ E'}
    {V₁ : A ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V : A ⥤ A₂}
    (s : J ≅ V₁ ⋙ J₁) (β : R ⋙ B ⟶ Q ⋙ R')
    (δ₁ : J₁ ⋙ Q ≅ V₂ ⋙ J₂) (δ : J ⋙ Q ≅ V ⋙ J₂) (c : V ≅ V₁ ⋙ V₂)
    (h : ∀ K, Q.map (s.hom.app K) ≫ δ₁.hom.app (V₁.obj K) =
      δ.hom.app K ≫ J₂.map (c.hom.app K)) :
    SourceIsoBeforeExchangeEquation
      (Functor.isoWhiskerRight s R ≪≫ Functor.associator V₁ J₁ R)
      (compositeExchange β δ₁) (compositeExchange β δ) c := by
  intro K
  have hn := β.naturality (s.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id,
    compositeExchange_app, Functor.comp_map]
  rw [← Category.assoc, hn, Category.assoc, ← R'.map_comp, h K, R'.map_comp]
  simp only [Category.assoc]

theorem source_before_open_from_pasting
    {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C] {I : B ⥤ B}
    (Q : B ⥤ C) (d : I ≅ 𝟭 B) {M N : B} {W Z : C}
    (δ : I.obj M ⟶ N) (s : M ⟶ N) (v : Q.obj N ⟶ Z)
    (γ : W ⟶ Q.obj (I.obj M)) (t : W ≅ Q.obj M) (p : W ⟶ Z) (q : Q.obj M ⟶ Z)
    (hs : s = d.inv.app M ≫ δ) (hγ : γ ≫ Q.map (d.hom.app M) = t.hom)
    (hp : γ ≫ Q.map δ ≫ v = p) (ht : t.hom ≫ q = p) :
    Q.map s ≫ v = q := by
  apply (cancel_epi t.hom).mp
  rw [ht, ← hp, ← hγ, hs]
  have hc : Q.map (d.hom.app M) ≫ Q.map (d.inv.app M ≫ δ) = Q.map δ := by
    rw [← Q.map_comp, Iso.hom_inv_id_app_assoc]
  simpa only [Category.assoc] using congrArg (fun z => γ ≫ z ≫ v) hc

theorem source_before_open_unit_component
    {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C] {I : B ⥤ B} {P Q : B ⥤ C}
    (c : P ≅ I ⋙ Q) (d : I ≅ 𝟭 B) (t : P ≅ Q)
    (h : c ≪≫ Functor.isoWhiskerRight d Q ≪≫ Functor.leftUnitor Q = t) (M : B) :
    c.hom.app M ≫ Q.map (d.hom.app M) = (t.app M).hom := by
  simpa only [Iso.app_hom, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.comp_obj,
    Functor.id_obj, Category.comp_id] using congrArg (fun z => z.hom.app M) h

theorem sourcePasting_target
    {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {E : Type uE} {E' : Type uE'} [Category.{vA} A]
    [Category.{vA₁} A₁] [Category.{vA₂} A₂]
    [Category.{vE} E] [Category.{vE'} E']
    {F : A ⥤ E} {F₁ : A₁ ⥤ E'} {F₂ F₂' : A₂ ⥤ E'} {B : E ⥤ E'}
    {V₁ : A ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V : A ⥤ A₂}
    (β₁ : F ⋙ B ⟶ V₁ ⋙ F₁) (β₂ : F ⋙ B ⟶ V ⋙ F₂)
    (β : F ⋙ B ⟶ V ⋙ F₂') (t : F₂' ⟶ F₂) (c : V ≅ V₁ ⋙ V₂)
    (s : F₁ ≅ V₂ ⋙ F₂)
    (hp : CompactifiedSourceIsoPastingEquation β₁ β₂ c s)
    (ht : TargetIsoBaseChangeEquation β₂ β t) :
    CompactifiedSourceIsoPastingEquation β₁ (β ≫ Functor.whiskerLeft V t) c s := by
  change β₂ = β ≫ Functor.whiskerLeft V t at ht
  exact ht ▸ hp

section CompositeExchangePasting
variable {A₀ : Type uA₀} {B₀ : Type uB₀} {C₀ : Type uC₀} {A₁ : Type uA₁} {B₁ : Type uB₁}
  {C₁ : Type uC₁} {A₂ : Type uA₂} {B₂ : Type uB₂} {C₂ : Type uC₂}
  [Category.{vA₀} A₀] [Category.{vB₀} B₀] [Category.{vC₀} C₀]
  [Category.{vA₁} A₁] [Category.{vB₁} B₁] [Category.{vC₁} C₁]
  [Category.{vA₂} A₂] [Category.{vB₂} B₂] [Category.{vC₂} C₂]
  {J₀ : A₀ ⥤ B₀} {R₀ : B₀ ⥤ C₀}
  {J₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ C₁}
  {J₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ C₂}
  {F₁ : A₀ ⥤ A₁} {H₁ : B₀ ⥤ B₁} {G₁ : C₀ ⥤ C₁}
  {F₂ : A₁ ⥤ A₂} {H₂ : B₁ ⥤ B₂} {G₂ : C₁ ⥤ C₂}
  {F₀₂ : A₀ ⥤ A₂} {H₀₂ : B₀ ⥤ B₂} {G₀₂ : C₀ ⥤ C₂}

/-- Combine the two original whole pasting equations before specializing any
of the derived-category carriers or actual compactified-map aliases. -/
theorem compositeExchange_pasting_of_equations
    (β₁ : R₀ ⋙ G₁ ⟶ H₁ ⋙ R₁) (β₂ : R₁ ⋙ G₂ ⟶ H₂ ⋙ R₂)
    (β₀₂ : R₀ ⋙ G₀₂ ⟶ H₀₂ ⋙ R₂)
    (e₁ : J₀ ⋙ H₁ ≅ F₁ ⋙ J₁) (e₂ : J₁ ⋙ H₂ ≅ F₂ ⋙ J₂)
    (e₀₂ : J₀ ⋙ H₀₂ ≅ F₀₂ ⋙ J₂)
    (γ : G₀₂ ≅ G₁ ⋙ G₂) (η : H₀₂ ≅ H₁ ⋙ H₂) (φ : F₀₂ ≅ F₁ ⋙ F₂)
    (θ₁ : (J₀ ⋙ R₀) ⋙ G₁ ⟶ F₁ ⋙ (J₁ ⋙ R₁))
    (θ₂ : (J₁ ⋙ R₁) ⋙ G₂ ⟶ F₂ ⋙ (J₂ ⋙ R₂))
    (θ₀₂ : (J₀ ⋙ R₀) ⋙ G₀₂ ⟶ F₀₂ ⋙ (J₂ ⋙ R₂))
    (hθ₁ : θ₁ = compositeExchange β₁ e₁)
    (hθ₂ : θ₂ = compositeExchange β₂ e₂)
    (hθ₀₂ : θ₀₂ = compositeExchange β₀₂ e₀₂)
    (hβ : ∀ K, ActualHorizontalMateEquation β₁ β₂ β₀₂ γ.hom η.hom K)
    (he : LeftComparisonPastingEquation e₁ e₂ e₀₂ φ η) (K : A₀) :
    ActualHorizontalMateEquation θ₁ θ₂ θ₀₂ γ.hom φ.hom K := by
  subst θ₁
  subst θ₂
  subst θ₀₂
  exact compositeExchange_pasting_app β₁ β₂ β₀₂ e₁ e₂ e₀₂
    γ.hom η.hom φ.hom K (hβ (J₀.obj K)) (he K)

end CompositeExchangePasting

end CategoryTheory
