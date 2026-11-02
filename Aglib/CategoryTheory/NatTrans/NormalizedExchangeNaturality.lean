/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Aglib.CategoryTheory.NatTrans.CompositeExchange

/-!
# Naturality of a normalized original exchange

Keep the original exchange square, normalization square, and whole formulas for
the normalized maps as separate inputs. This avoids unfolding concrete
isomorphism constructors while proving their naturality.
-/

@[expose] public section

universe uA vA uB vB uA' vA' uB' vB' uE vE uE' vE'

namespace CategoryTheory

variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
  [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
  {F₁ F₂ : A ⥤ B} {G : B ⥤ B'} {V : A ⥤ A'}
  {R₁ R₂ N₁ N₂ : A' ⥤ B'}

/-- Whole naturality of specified original exchanges between functor models. -/
def ExchangeNaturalityEquation (δ : F₂ ⟶ F₁)
    (β₁ : F₁ ⋙ G ⟶ V ⋙ R₁) (β₂ : F₂ ⋙ G ⟶ V ⋙ R₂)
    (δ' : R₂ ⟶ R₁) : Prop :=
  Functor.whiskerRight δ G ≫ β₁ = β₂ ≫ Functor.whiskerLeft V δ'

/-- Pasting actual normalization with an original exchange preserves naturality
for the specified normalized maps, using their whole defining formulas. -/
theorem normalizedExchangeNaturality
    (δ : F₂ ⟶ F₁) (β₁ : F₁ ⋙ G ⟶ V ⋙ R₁) (β₂ : F₂ ⋙ G ⟶ V ⋙ R₂)
    (δ' : R₂ ⟶ R₁) (n₁ : R₁ ⟶ N₁) (n₂ : R₂ ⟶ N₂) (δN : N₂ ⟶ N₁)
    (βN₁ : F₁ ⋙ G ⟶ V ⋙ N₁) (βN₂ : F₂ ⋙ G ⟶ V ⋙ N₂)
    (hraw : ExchangeNaturalityEquation δ β₁ β₂ δ')
    (hn : δ' ≫ n₁ = n₂ ≫ δN)
    (hβ₁ : βN₁ = β₁ ≫ Functor.whiskerLeft V n₁)
    (hβ₂ : βN₂ = β₂ ≫ Functor.whiskerLeft V n₂) :
    ExchangeNaturalityEquation δ βN₁ βN₂ δN := by
  change Functor.whiskerRight δ G ≫ βN₁ = βN₂ ≫ Functor.whiskerLeft V δN
  have hn' := congrArg (Functor.whiskerLeft V) hn
  simp only [Functor.whiskerLeft_comp] at hn'
  rw [hβ₁, hβ₂, ← Category.assoc, hraw, Category.assoc, hn', ← Category.assoc]

/-- Whole normalization equation for the proper exchange over identity maps. -/
def SourceIsoProperIdentityEquation
    {B : Type uB} {E : Type uE} [Category.{vB} B] [Category.{vE} E]
    {R : B ⥤ E} {IB : B ⥤ B} {IE : E ⥤ E}
    (β : R ⋙ IE ⟶ IB ⋙ R) (dB : IB ≅ 𝟭 B) (dE : IE ≅ 𝟭 E) : Prop :=
  ∀ M, β.app M ≫ R.map (dB.hom.app M) = dE.hom.app (R.obj M)

/-- Whole original source-transport exchange equation. -/
def SourceIsoExchangeEquation
    {A : Type uA} {A' : Type uA'} {E : Type uE}
    [Category.{vA} A] [Category.{vA'} A'] [Category.{vE} E]
    {F : A ⥤ E} {F' : A' ⥤ E} {V : A ⥤ A'} {IE : E ⥤ E}
    (β : F ⋙ IE ⟶ V ⋙ F') (dE : IE ≅ 𝟭 E) (s : F ≅ V ⋙ F') : Prop :=
  ∀ K, β.app K = dE.hom.app (F.obj K) ≫ s.hom.app K


/-- Whole source-transport naturality with the original comparison maps. -/
def SourceIsoNaturalityEquation
    {A : Type uA} {A' : Type uA'} {E : Type uE}
    [Category.{vA} A] [Category.{vA'} A'] [Category.{vE} E]
    {F₁ F₂ : A ⥤ E} {F₁' F₂' : A' ⥤ E} {V : A ⥤ A'}
    (t : F₂ ⟶ F₁) (t' : F₂' ⟶ F₁')
    (s₁ : F₁ ≅ V ⋙ F₁') (s₂ : F₂ ≅ V ⋙ F₂') : Prop :=
  t ≫ s₁.hom = s₂.hom ≫ Functor.whiskerLeft V t'


theorem sourceIsoExchange_of_proper_identity
    {A : Type uA} {A' : Type uA'} {B : Type uB} {E : Type uE}
    [Category.{vA} A] [Category.{vA'} A'] [Category.{vB} B] [Category.{vE} E]
    {J : A ⥤ B} {J' : A' ⥤ B} {V : A ⥤ A'} {R : B ⥤ E}
    {IB : B ⥤ B} {IE : E ⥤ E}
    (β : R ⋙ IE ⟶ IB ⋙ R) (dB : IB ≅ 𝟭 B) (dE : IE ≅ 𝟭 E)
    (δ : J ⋙ IB ≅ V ⋙ J')
    (hβ : SourceIsoProperIdentityEquation β dB dE) :
    SourceIsoExchangeEquation (compositeExchange β δ) dE
      (Functor.isoWhiskerRight
        ((Functor.rightUnitor J).symm ≪≫ Functor.isoWhiskerLeft J dB.symm ≪≫ δ) R ≪≫
        Functor.associator V J' R) := by
  intro K
  have hb := congrArg (fun t => t ≫ R.map (dB.inv.app (J.obj K))) (hβ (J.obj K))
  simp only [Category.assoc, ← R.map_comp, Iso.hom_inv_id_app, R.map_id,
    Functor.comp_obj, Functor.id_obj, Category.comp_id] at hb
  simp only [compositeExchange_app, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_inv_app, Functor.associator_hom_app, Category.id_comp,
    Category.comp_id, R.map_comp, Functor.comp_obj, Functor.id_obj]
  rw [hb, Category.assoc]


theorem sourceIsoNaturality_of_exchange
    {A : Type uA} {A' : Type uA'} {E : Type uE}
    [Category.{vA} A] [Category.{vA'} A'] [Category.{vE} E]
    {F₁ F₂ : A ⥤ E} {F₁' F₂' : A' ⥤ E} {V : A ⥤ A'} {I : E ⥤ E}
    (t : F₂ ⟶ F₁) (t' : F₂' ⟶ F₁')
    (β₁ : F₁ ⋙ I ⟶ V ⋙ F₁') (β₂ : F₂ ⋙ I ⟶ V ⋙ F₂') (d : I ≅ 𝟭 E)
    (s₁ : F₁ ≅ V ⋙ F₁') (s₂ : F₂ ≅ V ⋙ F₂')
    (h₁ : SourceIsoExchangeEquation β₁ d s₁) (h₂ : SourceIsoExchangeEquation β₂ d s₂)
    (hn : ExchangeNaturalityEquation t β₁ β₂ t') :
    SourceIsoNaturalityEquation t t' s₁ s₂ := by
  apply NatTrans.ext
  funext K
  have he := congrArg (fun z => z.app K) hn
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at he ⊢
  rw [h₁ K, h₂ K, ← Category.assoc, d.hom.naturality (t.app K)] at he
  exact (cancel_epi (d.hom.app (F₂.obj K))).mp
    (by simpa only [Functor.id_map, Category.assoc] using he)


theorem sourceIsoComponent_naturality
    {A : Type uA} {B : Type uB} {E : Type uE} [Category.{vA} A] [Category.{vB} B] [Category.{vE} E]
    {F₀ F₁ : A ⥤ E} {G₀ G₁ H₀ H₁ : B ⥤ E} (W : A ⥤ B)
    (t : F₀ ⟶ F₁) (u : G₀ ⟶ G₁) (v : H₀ ⟶ H₁)
    (s₀ : F₀ ≅ W ⋙ G₀) (s₁ : F₁ ≅ W ⋙ G₁)
    (m₀ : G₀ ≅ H₀) (m₁ : G₁ ≅ H₁)
    (hs : t ≫ s₁.hom = s₀.hom ≫ Functor.whiskerLeft W u)
    (hm : u ≫ m₁.hom = m₀.hom ≫ v) :
    t ≫ (s₁ ≪≫ Functor.isoWhiskerLeft W m₁).hom =
      (s₀ ≪≫ Functor.isoWhiskerLeft W m₀).hom ≫ Functor.whiskerLeft W v := by
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Category.assoc]
  rw [← Category.assoc, hs, Category.assoc, ← Functor.whiskerLeft_comp, hm,
    Functor.whiskerLeft_comp]


theorem isoComparison_model_transport
    {E : Type uE} {E' : Type uE'} [Category.{vE} E] [Category.{vE'} E'] (W : E ⥤ E')
    {A B C D : E} {F₀ F₁ : E'}
    (α : F₀ ≅ W.obj A) (β : F₁ ≅ W.obj B) (r : F₀ ≅ F₁)
    (u : A ≅ B) (v : B ≅ D) (w : A ≅ C) (z : C ≅ D)
    (hn : α ≪≫ W.mapIso u = r ≪≫ β) (hc : u ≪≫ v = w ≪≫ z) :
    r ≪≫ (β ≪≫ W.mapIso v) = (α ≪≫ W.mapIso w) ≪≫ W.mapIso z := by
  rw [← Iso.trans_assoc, ← hn, Iso.trans_assoc, ← W.mapIso_trans, hc,
    W.mapIso_trans, ← Iso.trans_assoc]


end CategoryTheory
