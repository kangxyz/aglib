/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.NormalizationNaturality

/-! # Original structural comparisons identify native composite normalizations -/
@[expose] public noncomputable section
open CategoryTheory
namespace CategoryTheory.Functor
universe u₁ u₂ u₃ v₁ v₂ v₃ d₁ d₂ d₃
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{d₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [EnoughInjectives B]
  [HasDerivedCategory.{d₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{d₃} C]
  (F : A ⥤ B) (G : B ⥤ C) (H P : A ⥤ C)
  [F.Additive] [G.Additive] [H.Additive] [P.Additive] [F.PreservesInjectiveObjects]

/-- Derive a proved ordinary structural triangle, without changing its composite comparison. -/
theorem derivedCompositeNormalizeOfPreservesInjectives_structural
    (e : P ≅ F ⋙ G) (t : F ⋙ G ≅ H) (q : P ≅ H) (h : e ≪≫ t = q) :
    derivedCompositeNormalizeOfPreservesInjectives F G H t =
      (P.rightDerivedFunctorPlusIso e ≪≫
        F.rightDerivedFunctorPlusCompIsoOfPreservesInjectives G).symm ≪≫
      P.rightDerivedFunctorPlusIso q := by
  rw [← h, rightDerivedFunctorPlusIso_trans]
  simp only [derivedCompositeNormalizeOfPreservesInjectives, Iso.trans_symm,
    Iso.trans_assoc, Iso.symm_self_id_assoc]
end CategoryTheory.Functor
