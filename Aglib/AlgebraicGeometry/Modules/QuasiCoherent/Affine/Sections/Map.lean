/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# The actual affine module global-sections map

The native affine section functor evaluates the original sheaf morphism at the
whole spectrum. These pointwise and whole-function formulas retain its original
scalar actions. Only consumers of these formulas import this leaf.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

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
