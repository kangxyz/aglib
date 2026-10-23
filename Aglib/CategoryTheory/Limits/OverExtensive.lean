/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Extensivity of slice categories

The original slice forgetful functor preserves coproducts and pullbacks and
reflects isomorphisms. Thus native finitary extensivity passes to slices.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Over

open Limits

universe u v

variable {C : Type u} [Category.{v} C]

/-- Slices of a finitary extensive category with pullbacks are finitary extensive. -/
instance finitaryExtensive [FinitaryExtensive C] [HasPullbacks C] (X : C) :
    FinitaryExtensive (Over X) :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism (forget X)

end CategoryTheory.Over
