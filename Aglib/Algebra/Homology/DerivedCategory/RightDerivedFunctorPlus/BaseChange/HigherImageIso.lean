/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ExactInputHomology
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology

/-! # Original higher-image comparison from exact-input derived exchange

Installed single and homology comparisons transport an actual derived
comparison isomorphism to the original higher right-derived functors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe uA vA uB vB uC vC uD vD wA wB wC wD

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B]
    [HasDerivedCategory.{wB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory.{wC} C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
    (F : A ⥤ B) (G : B ⥤ D) (K : A ⥤ C) (H : C ⥤ D)
    [F.Additive] [G.Additive] [K.Additive] [H.Additive]
    [G.PreservesHomology] [K.PreservesHomology]

/-- Original higher images compared through an actual derived exchange,
with exact input and output functors and all installed comparisons retained. -/
def higherImageIsoOfDerived (q : ℕ) (M : A)
    (e : G.rightDerivedFunctorPlus.obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M)) ≅
      H.rightDerivedFunctorPlus.obj
        (K.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M))) :
    G.obj ((F.rightDerived q).obj M) ≅ (H.rightDerived q).obj (K.obj M) :=
  G.mapIso ((F.rightDerivedSingleHomologyIso q).app M) ≪≫
    ((G.rightDerivedFunctorPlusHomologyIso (q : ℤ)).app
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M))).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor D (q : ℤ)).mapIso e ≪≫
    ((K.exactInputRightDerivedHomologyIso H q).app M).symm

end CategoryTheory.Functor
