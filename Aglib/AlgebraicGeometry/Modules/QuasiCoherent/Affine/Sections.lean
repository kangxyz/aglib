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
exactness, derived global sections, and strict-perfect module models. Its map
is the original sheaf morphism evaluated at the top open, both pointwise and as
an equality of underlying functions, with the original scalar actions retained.
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

variable {R : CommRingCat.{u}}

open Opposite in
/-- The original affine section map evaluates the same sheaf morphism at the top open. -/
theorem moduleSpecΓFunctor_map_apply {M N : (Spec R).Modules}
    (f : M ⟶ N) (m : Γ(M, ⊤)) :
    ((moduleSpecΓFunctor (R := R)).map f) m = f.val.app (op ⊤) m := by
  rfl

/-- The underlying function of the native affine section map is its top-section map. -/
theorem moduleSpecΓFunctor_map_coe {M N : (Spec R).Modules} (k : M ⟶ N) :
    (fun m : Γ(M, ⊤) => ((moduleSpecΓFunctor (R := R)).map k) m) =
      (fun m : Γ(M, ⊤) => (k.app ⊤) m) := by
  funext m
  exact moduleSpecΓFunctor_map_apply k m

end AlgebraicGeometry.Scheme.Modules
