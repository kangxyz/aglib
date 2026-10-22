/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-!
# Integral maps induced by valuation-preserving field maps
-/

@[expose] public noncomputable section

open scoped WithZero

namespace Valuation

variable {K L : Type*} [Field K] [Field L]
    (v : Valuation K ℤᵐ⁰) (w : Valuation L ℤᵐ⁰)

/-- The integral map attached to an actual isometric map of fields. -/
def integerMap (f : K →+* L) (hf : ∀ x, w (f x) = v x) :
    v.valuationSubring →+* w.valuationSubring where
  toFun x := ⟨f x, by change w (f (x : K)) ≤ 1; rw [hf]; exact x.property⟩
  map_zero' := Subtype.ext (map_zero f)
  map_one' := Subtype.ext (map_one f)
  map_add' x y := Subtype.ext (map_add f (x : K) (y : K))
  map_mul' x y := Subtype.ext (map_mul f (x : K) (y : K))


end Valuation
