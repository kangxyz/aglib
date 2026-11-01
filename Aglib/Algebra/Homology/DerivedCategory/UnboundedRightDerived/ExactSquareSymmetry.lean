/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactSquare

/-! # The original square of localized exact functors -/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃ u₄ v₄ w₄

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  {D : Type u₄} [Category.{v₄} D] [Abelian D] [HasDerivedCategory.{w₄} D]
  (F : A ⥤ B) (H : B ⥤ D) (G : A ⥤ C) (V : C ⥤ D)
  [F.Additive] [H.Additive] [G.Additive] [V.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  (e : G ⋙ V ≅ F ⋙ H)

/-- Transposition retains the original localized square, as a whole isomorphism. -/
theorem mapDerivedCategorySquareIso_symm :
    mapDerivedCategorySquareIso G V F H e.symm =
      (mapDerivedCategorySquareIso F H G V e).symm := by
  simp only [mapDerivedCategorySquareIso, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc]
  rfl

/-- Supplied original square representatives inherit transposition without expanding components. -/
theorem mapDerivedCategorySquareIso_transpose
    (e' : F ⋙ H ≅ G ⋙ V) (he : e' = e.symm)
    (s : G.mapDerivedCategory ⋙ V.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ H.mapDerivedCategory)
    (t : F.mapDerivedCategory ⋙ H.mapDerivedCategory ≅
      G.mapDerivedCategory ⋙ V.mapDerivedCategory)
    (hs : s = mapDerivedCategorySquareIso F H G V e)
    (ht : t = mapDerivedCategorySquareIso G V F H e') : t = s.symm := by
  rw [hs, ht, he]
  exact mapDerivedCategorySquareIso_symm F H G V e

end CategoryTheory.Functor
