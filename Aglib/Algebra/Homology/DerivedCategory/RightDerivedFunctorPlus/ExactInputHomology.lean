/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology

/-! # Exact input and homology of the original composed derived functors

An exact input functor need not preserve injectives. The comparison uses its
original exact-single isomorphism, followed by the original natural-degree
single/homology comparison of the outer functor. It does not replace the
composite derived functor by the derivative of the underived composite.
-/

@[expose] public noncomputable section

open CategoryTheory

universe uA vA uB vB uC vC wA wB wC

namespace CategoryTheory.Functor

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B]
    [HasDerivedCategory.{wB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    (K : A ⥤ B) [K.Additive] [K.PreservesHomology]
    (F : B ⥤ C) [F.Additive]

/-- Whole natural comparison for exact input and the unchanged outer right
 derivative. No preservation of injectives by the exact input is assumed. -/
def exactInputRightDerivedHomologyIso (q : ℕ) :
    K ⋙ F.rightDerived q ≅
      DerivedCategory.Plus.singleFunctor A 0 ⋙ K.rightDerivedFunctorPlus ⋙
        F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C (q : ℤ) :=
  Functor.isoWhiskerLeft K (F.rightDerivedSingleHomologyIso q) ≪≫
    (Functor.associator K (DerivedCategory.Plus.singleFunctor B 0)
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C (q : ℤ))).symm ≪≫
    Functor.isoWhiskerRight (K.rightDerivedFunctorPlusSingleIso 0).symm
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C (q : ℤ)) ≪≫
    Functor.associator (DerivedCategory.Plus.singleFunctor A 0) K.rightDerivedFunctorPlus
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C (q : ℤ))

end CategoryTheory.Functor
