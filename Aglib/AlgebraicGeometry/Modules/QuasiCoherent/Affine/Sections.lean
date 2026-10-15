/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
/-! # The actual affine module global-sections functor

The original `moduleSpecΓFunctor` is additive by its pointwise module maps over
every commutative ring. This provider supplies the same functor law to affine
exactness, derived global sections, and strict-perfect module models.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The original affine section functor is additive by its pointwise module maps. -/
instance moduleSpecΓFunctor_additive (R : CommRingCat.{u}) :
    (moduleSpecΓFunctor (R := R)).Additive where
  map_add := by intros; rfl

end AlgebraicGeometry.Scheme.Modules
