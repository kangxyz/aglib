/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.CompositionPredicate

/-! # Original open-compositor contractions from the proved compositor associativity -/

@[expose] public section
namespace CategoryTheory
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {F : A ⥤ B} {G : B ⥤ C} {H : C ⥤ D}
  {M : A ⥤ C} {N : B ⥤ D} {P P' : A ⥤ D}

/-- The two contractions of three original open factors use their specified original maps. -/
def OpenCompositionEquation (c₀₁ : F ⋙ G ≅ M) (c₁₂ : M ⋙ H ≅ P')
    (c₀₂ : F ⋙ N ≅ P') (cMN : G ⋙ H ≅ N) : Prop :=
  Functor.isoWhiskerRight c₀₁ H ≪≫ c₁₂ =
    Functor.associator F G H ≪≫ Functor.isoWhiskerLeft F cMN ≪≫ c₀₂

/-- The original associativity law gives the contraction law without a new coherence premise. -/
theorem openCompositionEquation_of_associates
    (e₀ : P ≅ P') (e₁ : P ≅ F ⋙ N) (e₂ : N ≅ G ⋙ H)
    (e₃ : P' ≅ M ⋙ H) (e₄ : M ≅ F ⋙ G)
    (h : Functor.CompositionAssociates e₀ e₁ e₂ e₃ e₄)
    (c₀₁ : F ⋙ G ≅ M) (c₁₂ : M ⋙ H ≅ P')
    (c₀₂ : F ⋙ N ≅ P') (cMN : G ⋙ H ≅ N)
    (h₀₁ : c₀₁ = e₄.symm) (h₁₂ : c₁₂ = e₃.symm)
    (h₀₂ : c₀₂ = e₁.symm ≪≫ e₀) (hMN : cMN = e₂.symm) :
    OpenCompositionEquation c₀₁ c₁₂ c₀₂ cMN := by
  subst c₀₁
  subst c₁₂
  subst c₀₂
  subst cMN
  have ht := congrArg (fun e => Functor.associator F G H ≪≫ e.symm ≪≫ e₀) h
  simp only [Iso.trans_symm, Functor.isoWhiskerLeft_symm,
    Functor.isoWhiskerRight_symm, Iso.trans_assoc, Iso.self_symm_id_assoc,
    Iso.symm_self_id, Iso.trans_refl] at ht
  exact ht.symm

end CategoryTheory
