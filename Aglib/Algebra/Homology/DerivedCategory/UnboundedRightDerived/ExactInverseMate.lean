/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactMate
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactSquareSymmetry

/-! # Whole original inverse-square mate after exact localization -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe uA vA wA uB vB wB uC vC wC uD vD wD

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {G : A ⥤ C} {H : B ⥤ D}
  [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
  [G.Additive] [H.Additive]
  [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The inverse of the specified original exact square retains its original mate.
Whole supplied derived representatives are substituted only in this abstract proof. -/
theorem mapDerivedCategorySquareIso_inverse_mate
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (e : L₁ ⋙ H ≅ G ⋙ L₂) (β : R₁ ⋙ G ≅ H ⋙ R₂)
    (h : (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)).natTrans = β.hom)
    (eD : L₁.mapDerivedCategory ⋙ H.mapDerivedCategory ≅
      G.mapDerivedCategory ⋙ L₂.mapDerivedCategory)
    (βD : R₁.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ R₂.mapDerivedCategory)
    (heD : eD = mapDerivedCategorySquareIso G L₂ L₁ H e)
    (hβD : βD = mapDerivedCategorySquareIso H R₂ R₁ G β) :
    (mateEquiv a.mapDerivedCategoryAdjunction b.mapDerivedCategoryAdjunction
      (TwoSquare.mk _ _ _ _ eD.inv)).natTrans = βD.hom := by
  subst eD
  subst βD
  have hs := mapDerivedCategorySquareIso_symm G L₂ L₁ H e
  have hm := mapDerivedCategorySquareIso_mate a b e.symm β h
  exact (congrArg (fun t : G.mapDerivedCategory ⋙ L₂.mapDerivedCategory ≅
      L₁.mapDerivedCategory ⋙ H.mapDerivedCategory =>
        (mateEquiv a.mapDerivedCategoryAdjunction b.mapDerivedCategoryAdjunction
          (TwoSquare.mk _ _ _ _ t.hom)).natTrans) hs).symm.trans hm

end CategoryTheory
