/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Grp.Resize.Diagram

/-! # Original additive values of a common-universe comparison square -/

@[expose] public section

namespace AddCommGrpCat

open CategoryTheory

universe uA uB

/-- Evaluate an actual naturality square through the same native ULift
comparisons, retaining both original group worlds and additive values. -/
theorem uliftComparison_naturality
    {A A' : AddCommGrpCat.{uA}} {B B' : AddCommGrpCat.{uB}}
    (E : AddCommGrpCat.uliftFunctor.{uB, uA}.obj A ≅
      AddCommGrpCat.uliftFunctor.{uA, uB}.obj B)
    (E' : AddCommGrpCat.uliftFunctor.{uB, uA}.obj A' ≅
      AddCommGrpCat.uliftFunctor.{uA, uB}.obj B')
    (a : A ⟶ A') (b : B ⟶ B')
    (h : E.hom ≫ AddCommGrpCat.uliftFunctor.map b =
      AddCommGrpCat.uliftFunctor.map a ≫ E'.hom) (x : A) :
    b ((AddEquiv.ulift.symm.trans
      (E.addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)) x) =
    (AddEquiv.ulift.symm.trans
      (E'.addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)) (a x) :=
  congrArg ULift.down (ConcreteCategory.congr_hom h (ULift.up x))

end AddCommGrpCat
