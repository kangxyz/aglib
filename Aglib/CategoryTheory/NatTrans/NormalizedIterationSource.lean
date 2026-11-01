/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.NormalizedExchangeNaturality
public import Aglib.CategoryTheory.NatTrans.RefinedSourcePasting
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uA₁ uA₂ uB uB' vA vA₁ vA₂ vB vB'

variable {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {B : Type uB} {B' : Type uB'}
  [Category.{vA} A] [Category.{vA₁} A₁] [Category.{vA₂} A₂] [Category.{vB} B] [Category.{vB'} B']
  {F : A ⥤ B} {G : B ⥤ B'} {V : A ⥤ A₁} {H : A ⥤ A₂} {E : A₁ ⥤ A₂}
  {R₁ N₁ : A₁ ⥤ B'} {R₂ R₃ N₂ N₃ : A₂ ⥤ B'}

/-- The original raw source/ambient equation and the actual normalization
triangle imply the same equation for the specified normalized exchanges. -/
theorem refinedSourceIsoPastingEquation_normalize
    (β : F ⋙ G ⟶ V ⋙ R₁) (β' : F ⋙ G ⟶ H ⋙ R₃)
    (η : H ≅ V ⋙ E) (s : R₁ ≅ E ⋙ R₂) (t : R₂ ⟶ R₃)
    (n₁ : R₁ ⟶ N₁) (n₂ : R₂ ⟶ N₂) (n₃ : R₃ ⟶ N₃)
    (sN : N₁ ≅ E ⋙ N₂) (tN : N₂ ⟶ N₃)
    (βN : F ⋙ G ⟶ V ⋙ N₁) (βN' : F ⋙ G ⟶ H ⋙ N₃)
    (hraw : RefinedSourceIsoPastingEquation β β' η s t)
    (hsource : SourceIsoNaturalityEquation n₁ n₂ sN s)
    (htriangle : t ≫ n₃ = n₂ ≫ tN)
    (hβ : βN = β ≫ Functor.whiskerLeft V n₁)
    (hβ' : βN' = β' ≫ Functor.whiskerLeft H n₃) :
    RefinedSourceIsoPastingEquation βN βN' η sN tN := by
  intro K
  have hf := congrArg (fun z => z.app K) hβ
  have hf' := congrArg (fun z => z.app K) hβ'
  have hs := congrArg (fun z => z.app (V.obj K)) hsource
  have ht := congrArg (fun z => z.app (E.obj (V.obj K))) htriangle
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf hf' hs ht
  have hn : n₃.app (H.obj K) ≫ N₃.map (η.hom.app K) =
      R₃.map (η.hom.app K) ≫ n₃.app (E.obj (V.obj K)) := by
    simpa only [Functor.comp_obj] using (n₃.naturality (η.hom.app K)).symm
  rw [hf', Category.assoc, hn]
  have hr := congrArg (fun z => z ≫ n₃.app (E.obj (V.obj K))) (hraw K)
  simp only [Category.assoc, Functor.comp_obj] at hr
  rw [hr, ht]
  rw [← Category.assoc (s.hom.app _) (n₂.app _) (tN.app _), ← hs]
  rw [hf]
  simp only [Category.assoc, Functor.comp_obj]

end CategoryTheory
