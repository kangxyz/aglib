/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.SpecUnitsTensor

/-! The product-coordinate equation uses arbitrary native commutative algebras. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory MonObj
open AlgebraicGeometry.Scheme.Group
open CartierDuality
open scoped TensorProduct CategoryTheory.MonObj

universe u

variable {R : Type u} [CommRing R]

local instance instCommGrpObjSpecUnitsTensorTest :
    CommGrpObj (MultiplicativeGroup.scheme (Spec (CommRingCat.of R))) :=
  MultiplicativeGroup.commGroup _

example (A : CommAlgCat.{u} R) (u : Aˣ) :
    (algSpecTensorIso A A).inv ≫ (specUnitMap A u ⊗ₘ specUnitMap A u) ≫
        μ[MultiplicativeGroup.scheme (Spec (CommRingCat.of R))] =
      specUnitMap (A ⊗ A)
        (Units.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toMonoidHom u *
          Units.map (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toMonoidHom u) :=
  specUnitMap_tensor_coordinates A u
