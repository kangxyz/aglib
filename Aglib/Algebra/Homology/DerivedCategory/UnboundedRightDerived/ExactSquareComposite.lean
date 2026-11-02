/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactSquare
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactCompositeCoherence

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

variable (M N : A ⥤ D) [M.Additive] [N.Additive]
  [PreservesFiniteLimits M] [PreservesFiniteColimits M]
  [PreservesFiniteLimits N] [PreservesFiniteColimits N]

/-- A square expressed by original compositors keeps that expression after exact deriving. -/
theorem mapDerivedCategorySquareIso_compositors
    (a : M ≅ G ⋙ V) (b : N ≅ F ⋙ H) (h : M = N)
    (he : e = a.symm ≪≫ eqToIso h ≪≫ b) :
    mapDerivedCategorySquareIso F H G V e =
      (mapDerivedCategoryCompositeIso G V M a).symm ≪≫
        eqToIso (by cases h; rfl : M.mapDerivedCategory = N.mapDerivedCategory) ≪≫
        mapDerivedCategoryCompositeIso F H N b := by
  subst N
  subst e
  change mapDerivedCategoryCompIso G V ≪≫
      mapDerivedCategoryOriginalIso (G ⋙ V) (F ⋙ H) (a.symm ≪≫ eqToIso rfl ≪≫ b) ≪≫
      (mapDerivedCategoryCompIso F H).symm = _
  simp only [eqToIso_refl, Iso.refl_trans,
    mapDerivedCategoryOriginalIso_trans, mapDerivedCategoryOriginalIso_symm,
    mapDerivedCategoryCompositeIso, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]

end CategoryTheory.Functor
