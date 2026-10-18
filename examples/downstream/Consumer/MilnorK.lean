/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK
public import Aglib.KTheory.MilnorK.CompatibilityK3

/-! A separate client of the uniform group and its nested low-degree comparisons. -/

@[expose] public section

noncomputable section

open MilnorK

universe u v

example (F : Type u) [Field F] : K F 0 ≃ₗ[ℤ] ℤ := zeroEquiv F

example (F : Type u) [Field F] : K F 1 ≃ₗ[ℤ] Additive Fˣ := oneEquiv F

example {F : Type u} {E : Type v} [Field F] [Field E]
    (n : ℕ) (f : F →+* E) (a : SymbolTuple F n) :
    map n f (symbol a) = symbol (fun i => Units.map f.toMonoidHom (a i)) :=
  map_symbol n f a

example (F : Type u) [Field F] : K F 2 ≃ₗ[ℤ] MilnorK.K2.Group F := twoEquiv F

example (F : Type u) [Field F] : K F 3 ≃ₗ[ℤ] MilnorK.K3.Group F := threeEquiv F

example {F : Type u} [Field F] (m n : ℕ)
    (a : SymbolTuple F m) (b : SymbolTuple F n) :
    product m n (symbol a) (symbol b) = symbol (Fin.append a b) :=
  product_symbol a b
