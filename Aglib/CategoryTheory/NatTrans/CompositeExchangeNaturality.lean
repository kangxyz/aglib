/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.NatIso

/-!
# Naturality of a pasted exchange with respect to original comparisons

The calculation retains the actual unit comparison, structural image
identification and exchanges. It combines their two original commuting squares;
concrete consumers must prove those squares, rather than postulate them as a
replacement for geometric compatibility.
-/

@[expose] public section

universe uU vU uC vC uD vD uS vS uU' vU' uC' vC' uD' vD' uT vT

namespace CategoryTheory

variable {U : Type uU} {C : Type uC} {D : Type uD} {S : Type uS}
  {U' : Type uU'} {C' : Type uC'} {D' : Type uD'} {T : Type uT}
  [Category.{vU} U] [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
  [Category.{vU'} U'] [Category.{vC'} C'] [Category.{vD'} D'] [Category.{vT} T]
  {J₁ : U ⥤ C} {J₂ : U ⥤ D} {R : C ⥤ D} {P₁ : C ⥤ S} {P₂ : D ⥤ S}
  {F : S ⥤ T} {V : U ⥤ U'} {Q₁ : C ⥤ C'} {Q₂ : D ⥤ D'}
  {R' : C' ⥤ D'} {P₁' : C' ⥤ T} {P₂' : D' ⥤ T}
  {J₁' : U' ⥤ C'} {J₂' : U' ⥤ D'}

/-- Naturality of pasted original exchanges follows from the original unit and
structural-image comparison squares. No invertibility hypothesis is needed. -/
theorem compositeExchange_comparison_naturality
    (δ : J₂ ⟶ J₁ ⋙ R) (δ' : J₂' ⟶ J₁' ⋙ R')
    (τ : R ⋙ P₂ ⟶ P₁) (τ' : R' ⋙ P₂' ⟶ P₁')
    (β₁ : P₁ ⋙ F ⟶ Q₁ ⋙ P₁') (β₂ : P₂ ⋙ F ⟶ Q₂ ⋙ P₂')
    (βR : R ⋙ Q₂ ⟶ Q₁ ⋙ R')
    (e₁ : J₁ ⋙ Q₁ ⟶ V ⋙ J₁') (e₂ : J₂ ⋙ Q₂ ⟶ V ⋙ J₂') (K : U)
    (hδ : Q₂.map (δ.app K) ≫ βR.app (J₁.obj K) ≫ R'.map (e₁.app K) =
      e₂.app K ≫ δ'.app (V.obj K))
    (hτ : F.map (τ.app (J₁.obj K)) ≫ β₁.app (J₁.obj K) =
      β₂.app (R.obj (J₁.obj K)) ≫ P₂'.map (βR.app (J₁.obj K)) ≫
        τ'.app (Q₁.obj (J₁.obj K))) :
    F.map (P₂.map (δ.app K) ≫ τ.app (J₁.obj K)) ≫
        β₁.app (J₁.obj K) ≫ P₁'.map (e₁.app K) =
      β₂.app (J₂.obj K) ≫ P₂'.map (e₂.app K) ≫
        (P₂'.map (δ'.app (V.obj K)) ≫ τ'.app (J₁'.obj (V.obj K))) := by
  have hn : F.map (P₂.map (δ.app K)) ≫ β₂.app (R.obj (J₁.obj K)) =
      β₂.app (J₂.obj K) ≫ P₂'.map (Q₂.map (δ.app K)) :=
    β₂.naturality (δ.app K)
  have ht : τ'.app (Q₁.obj (J₁.obj K)) ≫ P₁'.map (e₁.app K) =
      P₂'.map (R'.map (e₁.app K)) ≫ τ'.app (J₁'.obj (V.obj K)) :=
    (τ'.naturality (e₁.app K)).symm
  calc
    F.map (P₂.map (δ.app K) ≫ τ.app (J₁.obj K)) ≫
        β₁.app (J₁.obj K) ≫ P₁'.map (e₁.app K) =
      F.map (P₂.map (δ.app K)) ≫
        (F.map (τ.app (J₁.obj K)) ≫ β₁.app (J₁.obj K)) ≫
          P₁'.map (e₁.app K) := by simp only [Functor.map_comp, Category.assoc]
    _ = (F.map (P₂.map (δ.app K)) ≫ β₂.app (R.obj (J₁.obj K))) ≫
        P₂'.map (βR.app (J₁.obj K)) ≫
          (τ'.app (Q₁.obj (J₁.obj K)) ≫ P₁'.map (e₁.app K)) := by
            rw [hτ]
            simp only [Category.assoc]
    _ = β₂.app (J₂.obj K) ≫
        P₂'.map (Q₂.map (δ.app K) ≫ βR.app (J₁.obj K) ≫ R'.map (e₁.app K)) ≫
          τ'.app (J₁'.obj (V.obj K)) := by
            rw [hn, ht]
            simp only [Functor.map_comp, Category.assoc]
    _ = β₂.app (J₂.obj K) ≫ P₂'.map (e₂.app K) ≫
        (P₂'.map (δ'.app (V.obj K)) ≫ τ'.app (J₁'.obj (V.obj K))) := by
          rw [hδ]
          simp only [Functor.map_comp, Category.assoc]

end CategoryTheory
