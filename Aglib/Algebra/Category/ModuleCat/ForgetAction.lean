/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-! # Actual left scalars on the forgetful module functor

Noncentral left multiplication is additive rather than module-linear. Its
naturality with every original linear map defines a ring action on the whole
forgetful functor, without imposing commutativity on the coefficient ring.
-/

@[expose] public section
open CategoryTheory
namespace ModuleCat
universe r w
variable (R : Type r) [Ring R]

/-- Sectionwise left multiplication on the unchanged underlying additive groups. -/
def forgetScalar (a : R) :
    forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w} ⟶
      forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w} where
  app M := AddCommGrpCat.ofHom {
    toFun := fun x => a • x
    map_zero' := smul_zero a
    map_add' := smul_add a }
  naturality {M N} f := by
    ext x
    exact (f.hom.map_smul a x).symm

/-- The whole forgetful functor retains the original coefficient-ring action. -/
def forgetScalarAction : R →+* End (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) where
  toFun := forgetScalar R
  map_zero' := by
    apply NatTrans.ext
    funext M
    ext x
    exact zero_smul R (show M from x)
  map_one' := by
    apply NatTrans.ext
    funext M
    ext x
    exact one_smul R (show M from x)
  map_add' a b := by
    apply NatTrans.ext
    funext M
    ext x
    exact add_smul a b (show M from x)
  map_mul' a b := by
    apply NatTrans.ext
    funext M
    ext x
    exact mul_smul a b (show M from x)

end ModuleCat
