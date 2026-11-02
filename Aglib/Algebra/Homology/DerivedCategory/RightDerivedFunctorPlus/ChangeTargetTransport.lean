/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ChangeTargetComposition

/-! # Target coherence for an original transported composition isomorphism -/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus
namespace CategoryTheory.Functor
universe u v u' v' u'' v'' dA dB dC₀ dC₁
variable {A : Type u} {B : Type u'} {C : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} C]
  [Abelian A] [Abelian B] [Abelian C] [EnoughInjectives A] [EnoughInjectives B]
  (hA : HasDerivedCategory.{dA} A) (hB : HasDerivedCategory.{dB} B)
  (hC₀ : HasDerivedCategory.{dC₀} C) (hC₁ : HasDerivedCategory.{dC₁} C)
  (F : A ⥤ B) (G : B ⥤ C) (P : A ⥤ C)
  [F.Additive] [G.Additive] [P.Additive] [F.PreservesInjectiveObjects]

/-- Original deriving of the specified composition isomorphism in explicit native models. -/
abbrev rightDerivedFunctorPlusTransportCompModel (e : P ≅ F ⋙ G) :
    (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hC₀ P _ _) ≅
      (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hB F _ _) ⋙
        (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hC₀ G _ _) :=
  rightDerivedFunctorPlusIsoModel hA hC₀ P e ≪≫
    rightDerivedFunctorPlusCompIsoModel hA hB hC₀ F G

/-- Original transported composition also commutes with canonical target transport. -/
theorem rightDerivedFunctorPlusChangeTarget_transportComp (e : P ≅ F ⋙ G) :
    isoWhiskerRight (rightDerivedFunctorPlusTransportCompModel hA hB hC₀ F G P e)
        (canonicalEquivalence hC₀ hC₁).functor ≪≫
      associator _ _ _ ≪≫
      isoWhiskerLeft ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hB F _ _))
        (rightDerivedFunctorPlusChangeTarget hB hC₀ hC₁ G) =
    rightDerivedFunctorPlusChangeTarget hA hC₀ hC₁ P ≪≫
      rightDerivedFunctorPlusTransportCompModel hA hB hC₁ F G P e := by
  simp only [rightDerivedFunctorPlusTransportCompModel, isoWhiskerRight_trans, Iso.trans_assoc]
  rw [rightDerivedFunctorPlusChangeTarget_comp]
  rw [← Iso.trans_assoc, rightDerivedFunctorPlusChangeTarget_iso]
  simp only [Iso.trans_assoc]

end CategoryTheory.Functor
