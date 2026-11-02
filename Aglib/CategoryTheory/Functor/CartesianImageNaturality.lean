/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionMap
public import Aglib.CategoryTheory.Functor.ImageCompositionRestriction
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ComparisonFormulas

/-! # The original Cartesian composition maps satisfy the proved image-refinement cube -/

@[expose] public section
namespace CategoryTheory
variable {A A' B₀ B₁ C₀ C₁ M N₀ N₁ Z : Type*}
  [Category* A] [Category* A'] [Category* B₀] [Category* B₁] [Category* C₀] [Category* C₁]
  [Category* M] [Category* N₀] [Category* N₁] [Category* Z]
  {K₀ : A ⥤ B₀} {K₁ : A ⥤ B₁} {J₀ : A ⥤ C₀} {J₁ : A ⥤ C₁}
  {L₀ : B₀ ⥤ C₀} {L₁ : B₁ ⥤ C₁} {I₀ : M ⥤ N₀} {I₁ : M ⥤ N₁}
  {Q₀ : B₀ ⥤ M} {Q₁ : B₁ ⥤ M} {R₀ : C₀ ⥤ N₀} {R₁ : C₁ ⥤ N₁}
  {P₀ : N₀ ⥤ Z} {P₁ : N₁ ⥤ Z} {S₀ : C₀ ⥤ Z} {S₁ : C₁ ⥤ Z}
  {F : B₁ ⥤ B₀} {G : C₁ ⥤ C₀} {H : N₁ ⥤ N₀}

/-- Source restriction and the original formulas assemble the proved cube. -/
theorem cartesianImageNaturality (V : A' ⥤ A)
    (δK : K₀ ⟶ K₁ ⋙ F) (δI : I₀ ⟶ I₁ ⋙ H) (δJ : J₀ ⟶ J₁ ⋙ G)
    (σ₀ : Q₀ ⋙ I₀ ⟶ L₀ ⋙ R₀) (σ₁ : Q₁ ⋙ I₁ ⟶ L₁ ⋙ R₁)
    (c₀ : K₀ ⋙ L₀ ≅ J₀) (c₁ : K₁ ⋙ L₁ ≅ J₁)
    (q : F ⋙ Q₀ ≅ Q₁) (p : H ⋙ P₀ ≅ P₁)
    (s₀ : R₀ ⋙ P₀ ≅ S₀) (s₁ : R₁ ⋙ P₁ ≅ S₁) (t : G ⋙ S₀ ≅ S₁)
    (h : ImageCompositionRefinementEquation δK δI δJ σ₀ σ₁ c₀ c₁ q p s₀ s₁ t) :
    ImageCompositionNaturalityEquation
      (K₀ := V ⋙ K₀) (K₁ := V ⋙ K₁) (J₀ := V ⋙ J₀) (J₁ := V ⋙ J₁)
      (Q₀ := Q₀) (Q₁ := Q₁) (I₀ := I₀) (I₁ := I₁)
      (P₀ := P₀) (P₁ := P₁) (S₀ := S₀) (S₁ := S₁)
      (Functor.whiskerLeft V (imageComparison δK q))
      (imageComparison δI p)
      (Functor.whiskerLeft V (imageComparison δJ t))
      (imageCompositionMap (K := V ⋙ K₀) (J := V ⋙ J₀)
        (L := L₀) (Q := Q₀) (I := I₀) (R := R₀) (P := P₀) (S := S₀)
        σ₀ (Functor.isoWhiskerLeft V c₀) s₀)
      (imageCompositionMap (K := V ⋙ K₁) (J := V ⋙ J₁)
        (L := L₁) (Q := Q₁) (I := I₁) (R := R₁) (P := P₁) (S := S₁)
        σ₁ (Functor.isoWhiskerLeft V c₁) s₁) :=
  imageCompositionNaturalityEquation
    (K₀ := V ⋙ K₀) (K₁ := V ⋙ K₁) (J₀ := V ⋙ J₀) (J₁ := V ⋙ J₁)
    (Functor.whiskerLeft V δK) δI (Functor.whiskerLeft V δJ)
    σ₀ σ₁ (Functor.isoWhiskerLeft V c₀) (Functor.isoWhiskerLeft V c₁)
    q p s₀ s₁ t _ _ _ _ _
    (imageCompositionRefinementEquation_whiskerLeft δK δI δJ σ₀ σ₁ c₀ c₁ q p s₀ s₁ t V h)
    (imageComparisonFormula_whiskerLeft δK q V)
    (imageComparisonFormula δI p)
    (imageComparisonFormula_whiskerLeft δJ t V)
    (imageCompositionMap_formula (K := V ⋙ K₀) (J := V ⋙ J₀)
        (L := L₀) (Q := Q₀) (I := I₀) (R := R₀) (P := P₀) (S := S₀)
        σ₀ (Functor.isoWhiskerLeft V c₀) s₀)
    (imageCompositionMap_formula (K := V ⋙ K₁) (J := V ⋙ J₁)
        (L := L₁) (Q := Q₁) (I := I₁) (R := R₁) (P := P₁) (S := S₁)
        σ₁ (Functor.isoWhiskerLeft V c₁) s₁)

end CategoryTheory
