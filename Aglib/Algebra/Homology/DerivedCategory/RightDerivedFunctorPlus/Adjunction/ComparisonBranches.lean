/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition

/-! # Agreement of the two installed bounded-below composition comparisons -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃
namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B] [EnoughInjectives B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

/-- When both sufficient conditions apply, both native comparison constructions
are the same comparison, because they retain the same original two-unit equation. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesHomology_eq_ofPreservesInjectives
    [F.PreservesInjectiveObjects] [G.PreservesHomology] :
    rightDerivedFunctorPlusCompIsoOfPreservesHomology F G =
      rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G := by
  apply Iso.ext
  apply (F ⋙ G).rightDerivedFunctorPlus.rightDerived_ext (F ⋙ G).rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso A)
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, whiskerLeft_app]
  rw [rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app,
    rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app]

end CategoryTheory.Functor
