/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionRefinement
public import Mathlib.CategoryTheory.Whiskering

/-! # Assemble the whole original composition-refinement square

Specified original component formulas turn the proved component cube into the
whole natural-transformation equation. This boundary avoids expanding concrete
native functor maps in the final consumer.
-/

@[expose] public section

namespace CategoryTheory

section Formulas
variable {A B C Z : Type*} [Category* A] [Category* B] [Category* C] [Category* Z]

/-- A specified original image-refinement map retains its original component. -/
def ImageRefinementFormula {L₀ : A ⥤ B} {L₁ : A ⥤ C} {F : C ⥤ B}
    {R₀ : B ⥤ Z} {R₁ : C ⥤ Z}
    (δ : L₀ ⟶ L₁ ⋙ F) (e : F ⋙ R₀ ≅ R₁) (τ : L₀ ⋙ R₀ ⟶ L₁ ⋙ R₁) : Prop :=
  ∀ K, τ.app K = R₀.map (δ.app K) ≫ e.hom.app (L₁.obj K)

/-- A specified original composition map retains its original interchange and
both specified compositors. -/
def ImageCompositionFormula {M N : Type*} [Category* M] [Category* N]
    {K : A ⥤ B} {J : A ⥤ C} {L : B ⥤ C}
    {Q : B ⥤ M} {I : M ⥤ N} {R : C ⥤ N} {P : N ⥤ Z} {S : C ⥤ Z}
    (σ : Q ⋙ I ⟶ L ⋙ R) (c : K ⋙ L ≅ J) (s : R ⋙ P ≅ S)
    (α : K ⋙ Q ⋙ I ⋙ P ⟶ J ⋙ S) : Prop :=
  ∀ X, α.app X = P.map (σ.app (K.obj X)) ≫ P.map (R.map (c.hom.app X)) ≫
    s.hom.app (J.obj X)

end Formulas

variable {A B₀ B₁ C₀ C₁ M N₀ N₁ Z : Type*}
  [Category* A] [Category* B₀] [Category* B₁] [Category* C₀] [Category* C₁]
  [Category* M] [Category* N₀] [Category* N₁] [Category* Z]
  {K₀ : A ⥤ B₀} {K₁ : A ⥤ B₁} {J₀ : A ⥤ C₀} {J₁ : A ⥤ C₁}
  {L₀ : B₀ ⥤ C₀} {L₁ : B₁ ⥤ C₁} {I₀ : M ⥤ N₀} {I₁ : M ⥤ N₁}
  {Q₀ : B₀ ⥤ M} {Q₁ : B₁ ⥤ M} {R₀ : C₀ ⥤ N₀} {R₁ : C₁ ⥤ N₁}
  {P₀ : N₀ ⥤ Z} {P₁ : N₁ ⥤ Z} {S₀ : C₀ ⥤ Z} {S₁ : C₁ ⥤ Z}
  {F : B₁ ⥤ B₀} {G : C₁ ⥤ C₀} {H : N₁ ⥤ N₀}
  (δK : K₀ ⟶ K₁ ⋙ F) (δI : I₀ ⟶ I₁ ⋙ H) (δJ : J₀ ⟶ J₁ ⋙ G)
  (σ₀ : Q₀ ⋙ I₀ ⟶ L₀ ⋙ R₀) (σ₁ : Q₁ ⋙ I₁ ⟶ L₁ ⋙ R₁)
  (c₀ : K₀ ⋙ L₀ ≅ J₀) (c₁ : K₁ ⋙ L₁ ≅ J₁)
  (q : F ⋙ Q₀ ≅ Q₁) (p : H ⋙ P₀ ≅ P₁)
  (s₀ : R₀ ⋙ P₀ ≅ S₀) (s₁ : R₁ ⋙ P₁ ≅ S₁) (t : G ⋙ S₀ ≅ S₁)
  (τK : K₀ ⋙ Q₀ ⟶ K₁ ⋙ Q₁) (τI : I₀ ⋙ P₀ ⟶ I₁ ⋙ P₁)
  (τJ : J₀ ⋙ S₀ ⟶ J₁ ⋙ S₁)
  (α₀ : K₀ ⋙ Q₀ ⋙ I₀ ⋙ P₀ ⟶ J₀ ⋙ S₀)
  (α₁ : K₁ ⋙ Q₁ ⋙ I₁ ⋙ P₁ ⟶ J₁ ⋙ S₁)

/-- The literal whole composition-refinement square for the specified maps. -/
def ImageCompositionNaturalityEquation : Prop :=
  Functor.whiskerRight τK (I₀ ⋙ P₀) ≫
    Functor.whiskerLeft (K₁ ⋙ Q₁) τI ≫ α₁ = α₀ ≫ τJ

/-- Original component factorizations assemble the proved cube into a whole map equation. -/
theorem imageCompositionNaturalityEquation
    (hCube : ImageCompositionRefinementEquation δK δI δJ σ₀ σ₁ c₀ c₁ q p s₀ s₁ t)
    (hK : ImageRefinementFormula δK q τK) (hI : ImageRefinementFormula δI p τI)
    (hJ : ImageRefinementFormula δJ t τJ)
    (h₀ : ImageCompositionFormula σ₀ c₀ s₀ α₀)
    (h₁ : ImageCompositionFormula σ₁ c₁ s₁ α₁) :
    ImageCompositionNaturalityEquation τK τI τJ α₀ α₁ := by
  apply NatTrans.ext
  funext X
  change P₀.map (I₀.map (τK.app X)) ≫ τI.app (Q₁.obj (K₁.obj X)) ≫ α₁.app X =
    α₀.app X ≫ τJ.app X
  rw [hK, hI, hJ, h₀, h₁]
  simpa only [Category.assoc] using hCube X

end CategoryTheory
