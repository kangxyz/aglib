/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.CoefficientSquareIso

/-! # Named whole-functor data for square pasting -/

@[expose] public section
namespace CategoryTheory

variable {A B C D E T : Type*}
  [Category A] [Category B] [Category C] [Category D] [Category E] [Category T]
  {f : A ⥤ B} {h : C ⥤ D} {v₀ : A ⥤ C} {v₁ : B ⥤ D}
  {l : E ⥤ T} {p₀ : A ⥤ E} {p₁ : B ⥤ E} {q₀ : C ⥤ T} {q₁ : D ⥤ T}

/-- Paste the three sides of a square using their original associators. -/
def coefficientSquarePastingLeft (ty : q₀ ≅ h ⋙ q₁)
    (s : v₀ ⋙ h ≅ f ⋙ v₁) (e₁ : v₁ ⋙ q₁ ≅ p₁ ⋙ l) :
    v₀ ⋙ q₀ ≅ (f ⋙ p₁) ⋙ l :=
  Functor.isoWhiskerLeft v₀ ty ≪≫ (Functor.associator v₀ h q₁).symm ≪≫
    Functor.isoWhiskerRight s q₁ ≪≫ Functor.associator f v₁ q₁ ≪≫
    Functor.isoWhiskerLeft f e₁ ≪≫ (Functor.associator f p₁ l).symm

/-- Paste the other two sides, retaining their original comparison maps. -/
def coefficientSquarePastingRight (tx : p₀ ≅ f ⋙ p₁) (e₀ : v₀ ⋙ q₀ ≅ p₀ ⋙ l) :
    v₀ ⋙ q₀ ≅ (f ⋙ p₁) ⋙ l :=
  e₀ ≪≫ Functor.isoWhiskerRight tx l

lemma coefficientSquarePasting_of_morphisms
    (tx : p₀ ≅ f ⋙ p₁) (ty : q₀ ≅ h ⋙ q₁)
    (s : v₀ ⋙ h ≅ f ⋙ v₁) (e₀ : v₀ ⋙ q₀ ≅ p₀ ⋙ l)
    (e₁ : v₁ ⋙ q₁ ≅ p₁ ⋙ l)
    (hc : ∀ {M : A} {N : B} (φ : f.obj M ⟶ N),
      ty.hom.app (v₀.obj M) ≫ q₁.map (s.hom.app M ≫ v₁.map φ) ≫ e₁.hom.app N =
        e₀.hom.app M ≫ l.map (tx.hom.app M ≫ p₁.map φ)) :
    coefficientSquarePastingLeft ty s e₁ = coefficientSquarePastingRight tx e₀ :=
  isoPastingOfCoefficientMorphisms f h v₀ v₁ l p₀ p₁ q₀ q₁ tx ty s e₀ e₁ hc

lemma coefficientSquarePasting_morphism
    (tx : p₀ ≅ f ⋙ p₁) (ty : q₀ ≅ h ⋙ q₁)
    (s : v₀ ⋙ h ≅ f ⋙ v₁) (e₀ : v₀ ⋙ q₀ ≅ p₀ ⋙ l)
    (e₁ : v₁ ⋙ q₁ ≅ p₁ ⋙ l)
    (hc : coefficientSquarePastingLeft ty s e₁ = coefficientSquarePastingRight tx e₀)
    {M : A} {N : B} (φ : f.obj M ⟶ N) :
    ty.hom.app (v₀.obj M) ≫ q₁.map (s.hom.app M ≫ v₁.map φ) ≫ e₁.hom.app N =
      e₀.hom.app M ≫ l.map (tx.hom.app M ≫ p₁.map φ) :=
  coefficientSquareOfIsoPasting f h v₀ v₁ l p₀ p₁ q₀ q₁ tx ty s e₀ e₁ hc φ

end CategoryTheory
