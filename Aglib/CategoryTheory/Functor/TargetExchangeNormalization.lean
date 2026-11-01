/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.TargetExchangePostcomp
public import Aglib.CategoryTheory.Functor.TargetIdentityExchange

/-! # Target squares with their original source normalizer retained -/

@[expose] public noncomputable section
open CategoryTheory.Functor
namespace CategoryTheory
section Postcomp
variable {A B A' T₀ T₁ : Type*}
  [Category* A] [Category* B] [Category* A'] [Category* T₀] [Category* T₁]
  {F : A ⥤ B} {G₀ : B ⥤ T₀} {G₁ : B ⥤ T₁} {U : A ⥤ A'}
  {V₀ W₀ : A' ⥤ T₀} {V₁ W₁ : A' ⥤ T₁} {E : T₀ ⥤ T₁}

/-- Preserve the specified original source normalizer while appending target comparison. -/
theorem targetExchange_postcomp_normalized
    (β₀ : F ⋙ G₀ ≅ U ⋙ V₀) (β₁ : F ⋙ G₁ ≅ U ⋙ V₁)
    (δ₀ : V₀ ≅ W₀) (δ₁ : V₁ ≅ W₁)
    (s : G₀ ⋙ E ≅ G₁) (t : V₀ ⋙ E ≅ V₁) (w : W₀ ⋙ E ≅ W₁)
    (n : (F ⋙ G₀) ⋙ E ≅ F ⋙ G₁)
    (hn : n = associator _ _ _ ≪≫ isoWhiskerLeft F s)
    (hβ : isoWhiskerRight β₀ E ≪≫ associator _ _ _ ≪≫ isoWhiskerLeft U t = n ≪≫ β₁)
    (hδ : isoWhiskerRight δ₀ E ≪≫ w = t ≪≫ δ₁) :
    isoWhiskerRight (β₀ ≪≫ isoWhiskerLeft U δ₀) E ≪≫
        associator _ _ _ ≪≫ isoWhiskerLeft U w = n ≪≫ (β₁ ≪≫ isoWhiskerLeft U δ₁) := by
  subst n
  have hb := hβ
  simp only [Iso.trans_assoc] at hb
  simpa only [Iso.trans_assoc] using targetExchange_postcomp β₀ β₁ δ₀ δ₁ s t w hb hδ
end Postcomp

section Identity
variable {A B₀ B₁ A' : Type*}
  [Category* A] [Category* B₀] [Category* B₁] [Category* A']
  {F : A ⥤ B₀} {I : B₀ ⥤ B₀} {I' E : B₀ ⥤ B₁} {U : A ⥤ A'}
  {V₀ : A' ⥤ B₀} {V₁ : A' ⥤ B₁}

/-- Identity normalization uses the same specified original source normalizer. -/
theorem targetIdentityExchange_normalized
    (β₀ : F ⋙ I ≅ U ⋙ V₀) (β₁ : F ⋙ I' ≅ U ⋙ V₁)
    (s : I ⋙ E ≅ I') (t : V₀ ⋙ E ≅ V₁)
    (i : I ≅ 𝟭 B₀) (ι : I' ≅ E) (ψ : F ≅ U ⋙ V₀)
    (n : (F ⋙ I) ⋙ E ≅ F ⋙ I')
    (hn : n = associator _ _ _ ≪≫ isoWhiskerLeft F s)
    (m : F ⋙ I ≅ F) (hm : m = isoWhiskerLeft F i ≪≫ rightUnitor F)
    (hi : ι = s.symm ≪≫ isoWhiskerRight i E ≪≫ leftUnitor E)
    (hβ : β₀ = m ≪≫ ψ)
    (hs : isoWhiskerRight β₀ E ≪≫ associator _ _ _ ≪≫ isoWhiskerLeft U t = n ≪≫ β₁) :
    β₁ = isoWhiskerLeft F ι ≪≫
      (isoWhiskerRight ψ E ≪≫ associator _ _ _ ≪≫ isoWhiskerLeft U t) := by
  subst n
  subst m
  have hb := hβ
  simp only [Iso.trans_assoc] at hb
  apply targetIdentityExchange β₀ β₁ s t i ι ψ hi hb
  simpa only [Iso.trans_assoc] using hs
end Identity
end CategoryTheory
