/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.Whole
public import Aglib.CategoryTheory.NatTrans.RefinedSourcePasting
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uA₁ uA₂ uAs uB uB₁ uB₂ vA vA₁ vA₂ vAs vB vB₁ vB₂

variable {A : Type uA} {A₁ : Type uA₁} {A₂ : Type uA₂} {As : Type uAs} {B : Type uB}
  {B₁ : Type uB₁} {B₂ : Type uB₂}
  [Category.{vA} A] [Category.{vA₁} A₁] [Category.{vA₂} A₂] [Category.{vAs} As]
  [Category.{vB} B] [Category.{vB₁} B₁] [Category.{vB₂} B₂]
  {F : A ⥤ B} {F₁ : A₁ ⥤ B₁} {F₂ Ft : A₂ ⥤ B₂} {Fs : As ⥤ B₂}
  {G₁ : B ⥤ B₁} {G₂ : B₁ ⥤ B₂} {G : B ⥤ B₂}
  {H₁ : A ⥤ A₁} {H₂ : A₁ ⥤ A₂} {H : A ⥤ A₂} {V : A ⥤ As} {E : As ⥤ A₂}

/-- The original two normalized steps, transported through both specified
source compositors, equal the specified one-step source/target comparison. -/
def OriginalNormalizedIterationEquation
    (β₁ : F ⋙ G₁ ⟶ H₁ ⋙ F₁) (β₂ : F₁ ⋙ G₂ ⟶ H₂ ⋙ F₂)
    (βs : F ⋙ G ⟶ V ⋙ Fs) (γ : G ≅ G₁ ⋙ G₂)
    (δ : H ≅ H₁ ⋙ H₂) (η : H ≅ V ⋙ E) (s : Fs ≅ E ⋙ Ft) (t : Ft ⟶ F₂) : Prop :=
  ∀ K, γ.hom.app (F.obj K) ≫ G₂.map (β₁.app K) ≫ β₂.app (H₁.obj K) ≫
      F₂.map ((δ.symm ≪≫ η).hom.app K) =
    βs.app K ≫ s.hom.app (V.obj K) ≫ t.app ((V ⋙ E).obj K)

/-- Both input equations concern the original maps, and imply the exact
normalized iteration equation by cancellation of the specified compositor. -/
theorem originalNormalizedIterationEquation_of_pasting
    (β₁ : F ⋙ G₁ ⟶ H₁ ⋙ F₁) (β₂ : F₁ ⋙ G₂ ⟶ H₂ ⋙ F₂)
    (βs : F ⋙ G ⟶ V ⋙ Fs) (β : F ⋙ G ⟶ H ⋙ F₂)
    (γ : G ≅ G₁ ⋙ G₂) (δ : H ≅ H₁ ⋙ H₂) (η : H ≅ V ⋙ E)
    (s : Fs ≅ E ⋙ Ft) (t : Ft ⟶ F₂)
    (hp : ∀ K, ActualHorizontalMateEquation β₁ β₂ β γ.hom δ.hom K)
    (hs : RefinedSourceIsoPastingEquation βs β η s t) :
    OriginalNormalizedIterationEquation β₁ β₂ βs γ δ η s t := by
  intro K
  have hd : δ.hom.app K ≫ (δ.symm ≪≫ η).hom.app K = η.hom.app K := by
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  calc
    γ.hom.app (F.obj K) ≫ G₂.map (β₁.app K) ≫ β₂.app (H₁.obj K) ≫
        F₂.map ((δ.symm ≪≫ η).hom.app K) =
      (β.app K ≫ F₂.map (δ.hom.app K)) ≫ F₂.map ((δ.symm ≪≫ η).hom.app K) := by
        simpa only [Category.assoc] using
          congrArg (fun z => z ≫ F₂.map ((δ.symm ≪≫ η).hom.app K))
            (actualHorizontalMateEquation_eq β₁ β₂ β γ.hom δ.hom K (hp K))
    _ = β.app K ≫ F₂.map (δ.hom.app K ≫ (δ.symm ≪≫ η).hom.app K) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = β.app K ≫ F₂.map (η.hom.app K) := by rw [hd]
    _ = βs.app K ≫ s.hom.app (V.obj K) ≫ t.app ((V ⋙ E).obj K) := hs K

end CategoryTheory
