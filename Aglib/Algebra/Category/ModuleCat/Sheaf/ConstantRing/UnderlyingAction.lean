/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantCoefficients
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.Algebra.Category.Grp.Preadditive

/-! # Noncommutative scalars on original underlying module sheaves

Multiplication by a scalar need not be linear over a noncommutative ring.
It is nevertheless a natural additive endomorphism of the actual underlying
abelian-sheaf functor. This is the correct scalar action for applying arbitrary
additive cohomological functors without assuming a linear coefficient category.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace ModuleCat.Sheaf

universe u v r
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type r) [Ring R]

attribute [local instance] hasSheafify

/-- Original sectionwise left multiplication, regarded only as an additive map. -/
def underlyingScalar (a : R) : underlying R J ⟶ underlying R J where
  app F := {
    hom := {
      app U := AddCommGrpCat.ofHom {
        toFun := fun x => a • x
        map_zero' := smul_zero a
        map_add' := smul_add a }
      naturality {U V} f := by
        ext x
        exact ((F.obj.map f).hom.map_smul a x).symm } }
  naturality {F G} f := by
    ext U x
    exact ((f.hom.app U).hom.map_smul a x).symm

/-- The coefficient ring acts on the unchanged whole underlying functor,
with categorical composition in the correct order for left modules. -/
def underlyingScalarAction : R →+* End (underlying R J) where
  toFun := underlyingScalar J R
  map_zero' := by
    apply NatTrans.ext
    funext F
    ext U x
    exact zero_smul R (show F.obj.obj U from x)
  map_one' := by
    apply NatTrans.ext
    funext F
    ext U x
    exact one_smul R (show F.obj.obj U from x)
  map_add' a b := by
    apply NatTrans.ext
    funext F
    ext U x
    exact add_smul a b (show F.obj.obj U from x)
  map_mul' a b := by
    apply NatTrans.ext
    funext F
    ext U x
    exact mul_smul a b (show F.obj.obj U from x)

/-- The scalar action changes neither the underlying sheaf nor its sections. -/
theorem underlyingScalarAction_apply (a : R)
    (F : Sheaf J (ModuleCat.{max u v} R)) (U : Cᵒᵖ) (x : F.obj.obj U) :
    (((underlyingScalarAction J R a).app F).hom.app U) x = a • x := rfl

end ModuleCat.Sheaf
