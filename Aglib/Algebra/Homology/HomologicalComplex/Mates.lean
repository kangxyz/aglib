/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.HomologicalComplex.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Original adjunction mates act degreewise on complexes -/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {G : A ⥤ C} {H : B ⥤ D}
  [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
  [G.Additive] [H.Additive]

/-- Degreewise application preserves the actual specified adjunction mate. -/
theorem mapHomologicalComplex_mate
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (β : R₁ ⋙ G ⟶ H ⋙ R₂)
    (h : (mateEquiv a b (TwoSquare.mk _ _ _ _ α)).natTrans = β)
    {ι : Type*} (c : ComplexShape ι) :
    (mateEquiv (a.mapHomologicalComplex c) (b.mapHomologicalComplex c)
      (TwoSquare.mk (G.mapHomologicalComplex c) _ _ (H.mapHomologicalComplex c)
        (α.mapHomologicalComplex c))).natTrans =
      β.mapHomologicalComplex c := by
  ext K n
  have hn := congrArg (fun t => t.app (K.X n)) h
  simpa [mateEquiv, Adjunction.mapHomologicalComplex] using hn

end CategoryTheory
