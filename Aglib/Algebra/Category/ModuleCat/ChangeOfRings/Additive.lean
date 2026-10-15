/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Additivity of scalar extension

The native scalar-extension functor is additive, including when the rings and
module carriers have independent universe levels. This proof uses its literal
pure-tensor formula and does not require a chosen adjunction universe.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S]

/-- Extension of scalars is additive for modules in an independent universe. -/
instance extendScalars_additive (φ : R →+* S) :
    (extendScalars.{u, w, v} φ).Additive where
  map_add {M N} f g := by
    apply ExtendScalars.hom_ext
    intro m
    let := φ.toAlgebra
    change (1 : S) ⊗ₜ[R] (f m + g m) =
      (1 : S) ⊗ₜ[R] f m + (1 : S) ⊗ₜ[R] g m
    exact TensorProduct.tmul_add _ _ _

end ModuleCat
