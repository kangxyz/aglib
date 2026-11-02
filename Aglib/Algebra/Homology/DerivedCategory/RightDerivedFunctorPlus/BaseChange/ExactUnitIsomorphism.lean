/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ActualZeroComparison
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Postcomposition
public import Aglib.Algebra.Homology.CochainComplexPlus.NatTrans

/-! # Invertibility of the original exact derived exchange

The actual original unit equation detects invertibility on localized complexes.
Exactness makes the two original derived units invertible, and localization
reflects the resulting natural isomorphism. All four selected category worlds
remain independent; no replacement exchange is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃ u₄ v₄ w₄

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B] [EnoughInjectives B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  {D : Type u₄} [Category.{v₄} D] [Abelian D] [HasDerivedCategory.{w₄} D]
  [EnoughInjectives D]
  (R₁ : B ⥤ A) (R₂ : D ⥤ C) (G : A ⥤ C) (H : B ⥤ D)
  [R₁.Additive] [R₂.Additive] [G.Additive] [H.Additive]
  [G.PreservesHomology] [H.PreservesHomology]
  [R₁.PreservesHomology] [R₂.PreservesHomology]
  (α : R₁ ⋙ G ⟶ H ⋙ R₂) [IsIso α]
  (β : R₁.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ⟶
    H.rightDerivedFunctorPlus ⋙ R₂.rightDerivedFunctorPlus)

/-- An invertible ordinary exchange and the actual unit equation force derived exchange
invertibility when both original direct-image functors are exact. -/
theorem isIso_of_actualDerivedUnitEquation
    (hunit : ∀ K, ActualDerivedUnitEquation R₁ R₂ G H α β K) : IsIso β := by
  let : IsIso R₁.rightDerivedFunctorPlusUnit :=
    R₁.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let : IsIso R₂.rightDerivedFunctorPlusUnit :=
    R₂.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have hcomponent (K : CochainComplex.Plus B) :
      IsIso (β.app (DerivedCategory.Plus.Q.obj K)) := by
    have : IsIso (α.mapCochainComplexPlus.app K) :=
      NatTrans.isIso_mapCochainComplexPlus_app α K (fun _ => inferInstance)
    have : IsIso ((exchangeOnComplexes R₁ R₂ G H α).app K) := by
      dsimp only [exchangeOnComplexes, NatTrans.comp_app]
      infer_instance
    have he := hunit K
    dsimp only [ActualDerivedUnitEquation] at he
    have hi : IsIso (G.rightDerivedFunctorPlus.map (R₁.rightDerivedFunctorPlusUnit.app K) ≫
        β.app (DerivedCategory.Plus.Q.obj K) ≫
        R₂.rightDerivedFunctorPlus.map
          (H.rightDerivedFunctorPlusExactComparison.hom.app K)) := by
      rw [he]
      infer_instance
    exact (isIso_comp_right_iff _ _).mp ((isIso_comp_left_iff _ _).mp hi)
  let W := (whiskeringLeft (CochainComplex.Plus B) (DerivedCategory.Plus B)
    (DerivedCategory.Plus C)).obj DerivedCategory.Plus.Q
  have : W.Full := Localization.full_whiskeringLeft DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso B) (DerivedCategory.Plus C)
  have : W.Faithful := Localization.faithful_whiskeringLeft DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso B) (DerivedCategory.Plus C)
  have : IsIso (W.map β) := by
    have (K : CochainComplex.Plus B) : IsIso ((W.map β).app K) := hcomponent K
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_fully_faithful W β

end CategoryTheory.Functor
