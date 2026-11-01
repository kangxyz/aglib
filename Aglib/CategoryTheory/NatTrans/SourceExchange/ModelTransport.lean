/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.ExchangePastingTransport
public import Aglib.CategoryTheory.NatTrans.SourceIsoComposition
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uB uE uA₁ uA₂ uA' uB' uD vA vB vE vA₁ vA₂ vA' vB' vD

theorem sourceIso_refinement_factor
    {A : Type uA} {B : Type uB} {E : Type uE} [Category.{vA} A] [Category.{vB} B]
    [Category.{vE} E] (W : A ⥤ B)
    {F : A ⥤ E} {G H I : B ⥤ E}
    (s : F ≅ W ⋙ G) (m : G ≅ H) (c : H ≅ I) (n : G ≅ I)
    (t : H ⟶ I) (hc : c.hom = t) (hn : m.hom ≫ t = n.hom) :
    (s ≪≫ Functor.isoWhiskerLeft W m) ≪≫ Functor.isoWhiskerLeft W c =
      s ≪≫ Functor.isoWhiskerLeft W n := by
  have hi : m ≪≫ c = n := by
    apply Iso.ext
    simpa only [Iso.trans_hom, hc] using hn
  rw [Iso.trans_assoc, ← Functor.isoWhiskerLeft_trans, hi]

theorem sourceComposition_replaceFirst
    {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {E : Type uE} [Category.{vA} A]
    [Category.{vA₁} A₁] [Category.{vA₂} A₂] [Category.{vE} E]
    {F : A ⥤ E} {F₁ : A₁ ⥤ E} {F₂ : A₂ ⥤ E}
    {V₁ : A ⥤ A₁} {V₂ : A₁ ⥤ A₂} {V : A ⥤ A₂}
    (s₁ s₁' : F ≅ V₁ ⋙ F₁) (s₂ s₂' : F₁ ≅ V₂ ⋙ F₂)
    (s : F ≅ V ⋙ F₂) (c : V ≅ V₁ ⋙ V₂)
    (h₁ : s₁' = s₁) (h₂ : s₂' = s₂)
    (h : SourceIsoCompositionEquation s₁ s₂ s (𝟙 F₂) c) :
    SourceIsoCompositionEquation s₁' s₂' s (𝟙 F₂) c := by
  subst s₁' s₂'
  exact h

theorem exchangeModelComparisonEquation_of_self
    {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'} [Category.{vA} A]
    [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
    {R M : A ⥤ B} {R' M' : A' ⥤ B'} (G : B ⥤ B') (H : A ⥤ A')
    (c : R ≅ M) (c' : R' ≅ M') (β : R ⋙ G ≅ H ⋙ R') (μ : M ⋙ G ≅ H ⋙ M')
    (d : M' ≅ M') (hd : d = Iso.refl M')
    (h : Functor.isoWhiskerRight c G ≪≫ (μ ≪≫ Functor.isoWhiskerLeft H d) =
      β ≪≫ Functor.isoWhiskerLeft H c') :
    ExchangeModelComparisonEquation c c' β.hom μ.hom := by
  apply exchangeModelComparisonEquation_of_iso
  simpa only [hd, Functor.isoWhiskerLeft_refl, Iso.trans_refl] using h

theorem sourceRefinement_model_equation
    {A : Type uA} {B : Type uB} {D : Type uD} [Category.{vA} A] [Category.{vB} B] [Category.{vD} D]
    (E : A ⥤ B) {F M : A ⥤ D} {N Mt M₂ : B ⥤ D}
    (cs : F ≅ M) (ψ : F ≅ E ⋙ N) (c₂ : N ≅ M₂)
    (s : M ≅ E ⋙ Mt) (d : M ≅ E ⋙ M₂)
    (t u : Mt ⟶ M₂) (hu : IsIso u)
    (hd : d = s ≪≫ Functor.isoWhiskerLeft E (@asIso _ _ _ _ u hu))
    (ht : t = u) (h : cs ≪≫ d = ψ ≪≫ Functor.isoWhiskerLeft E c₂) :
    cs.hom ≫ s.hom ≫ Functor.whiskerLeft E t =
      ψ.hom ≫ Functor.whiskerLeft E c₂.hom := by
  subst d
  subst t
  exact congrArg Iso.hom h

end CategoryTheory
