/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.Normalization

/-!
# Horizontal cube normalization for native mates

A compatible cube of left-adjoint squares yields the comparison between its
horizontal mate pastings. This is independent of any derived category model.
-/

@[expose] public section

namespace CategoryTheory

open TwoSquare

variable {A B C D A' B' C' D' : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* A'] [Category* B'] [Category* C'] [Category* D']
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {L₁' : A' ⥤ B'} {R₁' : B' ⥤ A'} {L₂' : C' ⥤ D'} {R₂' : D' ⥤ C'}
  {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}

/-- A compatible cube of left-adjoint squares gives the original-unit comparison
between its two horizontal composites of native mates. -/
theorem mateEquiv_horizontal_cube
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
    (s₁ : TwoSquare QA L₁ L₁' QB) (s₂ : TwoSquare QC L₂ L₂' QD)
    (α : TwoSquare G L₁ L₂ H) (α' : TwoSquare G' L₁' L₂' H')
    (γ : QA ⋙ G' ⟶ G ⋙ QC) (δ : QB ⋙ H' ⟶ H ⋙ QD)
    (h : ∀ X, L₂'.map (γ.app X) ≫ (α ≫ₕ s₂).app X =
      (s₁ ≫ₕ α').app X ≫ δ.app (L₁.obj X)) (K : B) :
    G'.map ((mateEquiv adj₁ adj₁' s₁).app K) ≫
        (mateEquiv adj₁' adj₂' α').app (QB.obj K) ≫ R₂'.map (δ.app K) =
      γ.app (R₁.obj K) ≫ QC.map ((mateEquiv adj₁ adj₂ α).app K) ≫
        (mateEquiv adj₂ adj₂' s₂).app (H.obj K) := by
  have hm := mateEquiv_top_bottom_naturality adj₁ adj₂'
    (s₁ ≫ₕ α') (α ≫ₕ s₂) γ δ h K
  rw [mateEquiv_hComp_app adj₁ adj₂ adj₂',
    mateEquiv_hComp_app adj₁ adj₁' adj₂'] at hm
  simpa only [Category.assoc] using hm.symm

end CategoryTheory
