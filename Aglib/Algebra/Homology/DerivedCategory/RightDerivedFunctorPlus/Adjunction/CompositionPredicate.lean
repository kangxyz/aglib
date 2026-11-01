/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.TransportedComposition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Transport

/-! # A typed boundary for associativity of specified derived comparisons

The predicate keeps the original five comparisons opaque at concrete call
sites. The transport theorem is proved once for abstract functors; no concrete
site or extension functor is unfolded by its consumers.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

section Predicate
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {F : A ⥤ B} {G : B ⥤ C} {H : C ⥤ D}
  {M : A ⥤ C} {N : B ⥤ D} {P P' : A ⥤ D}

/-- The specified compositors associate with their specified total transport. -/
def CompositionAssociates (e₀ : P ≅ P') (e₁ : P ≅ F ⋙ N) (e₂ : N ≅ G ⋙ H)
    (e₃ : P' ≅ M ⋙ H) (e₄ : M ≅ F ⋙ G) : Prop :=
  e₁ ≪≫ isoWhiskerLeft F e₂ =
    e₀ ≪≫ e₃ ≪≫ isoWhiskerRight e₄ H ≪≫ associator F G H

end Predicate

universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃ u₄ v₄ w₄
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B] [EnoughInjectives B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  [EnoughInjectives C] {D : Type u₄} [Category.{v₄} D] [Abelian D]
  [HasDerivedCategory.{w₄} D]
  (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
  (M : A ⥤ C) (N : B ⥤ D) (P P' : A ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [M.Additive] [N.Additive]
  [P.Additive] [P'.Additive]

/-- Abstract native deriving preserves the same typed associativity predicate. -/
theorem rightDerivedFunctorPlus_compositionAssociates
    [G.PreservesHomology] [H.PreservesHomology] [N.PreservesHomology]
    [(G ⋙ H).PreservesHomology]
    (e₀ : P ≅ P') (e₁ : P ≅ F ⋙ N) (e₂ : N ≅ G ⋙ H)
    (e₃ : P' ≅ M ⋙ H) (e₄ : M ≅ F ⋙ G)
    (hc : CompositionAssociates e₀ e₁ e₂ e₃ e₄)
    (d₀ : P.rightDerivedFunctorPlus ≅ P'.rightDerivedFunctorPlus)
    (hd₀ : d₀ = P.rightDerivedFunctorPlusIso e₀) :
    CompositionAssociates d₀
      (P.rightDerivedFunctorPlusIso e₁ ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesHomology F N)
      (N.rightDerivedFunctorPlusIso e₂ ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesHomology G H)
      (P'.rightDerivedFunctorPlusIso e₃ ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesHomology M H)
      (M.rightDerivedFunctorPlusIso e₄ ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesHomology F G) := by
  subst d₀
  have hc' : e₁ ≪≫ isoWhiskerLeft F e₂ =
      (e₀ ≪≫ e₃) ≪≫ isoWhiskerRight e₄ H ≪≫ associator F G H := by
    simpa only [CompositionAssociates, Iso.trans_assoc] using hc
  have h := rightDerivedFunctorPlusCompIsoOfPreservesHomology_transportAssoc
    F G H M N P e₁ e₂ (e₀ ≪≫ e₃) e₄ hc'
  simpa only [CompositionAssociates, rightDerivedFunctorPlusIso_trans,
    Iso.trans_assoc] using h

end CategoryTheory.Functor
