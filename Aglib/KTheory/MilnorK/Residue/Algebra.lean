/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.Specialization

/-!
# Right-unit multiplication for the residue construction

The tame recursion multiplies a class in degree `n` by an additive residue
unit on the right. This file provides that actual bilinear quotient map and
its two-slot Steinberg compatibility, with no degree-identification premise.
-/

@[expose] public noncomputable section

namespace MilnorK

universe u v

variable {F : Type u} [Field F]

/-- Multiplication of an actual degree `n` class by a unit on the right. -/
def productUnit (n : ℕ) : K F n →ₗ[ℤ] Additive Fˣ →ₗ[ℤ] K F (n + 1) :=
  (product n 1).compl₁₂ LinearMap.id (unitsToOne F)

/-- On symbols, right-unit multiplication appends the chosen coordinate. -/
@[simp] theorem productUnit_symbol (n : ℕ) (a : SymbolTuple F n) (b : Additive Fˣ) :
    productUnit n (symbol a) b = symbol (Fin.snoc a b.toMul) := by
  change product n 1 (symbol a) (symbol (fun _ => b.toMul)) = _
  rw [product_symbol, Fin.append_right_eq_snoc]

/-- Multiplying the degree-zero generator gives the ordinary degree-one symbol. -/
theorem productUnit_empty (b : Additive Fˣ) :
    productUnit 0 (symbol (F := F) Fin.elim0) b = unitsToOne F b := by
  rw [productUnit_symbol]
  rfl

/-- Two successive right-unit factors kill every actual degree-two Milnor relation. -/
theorem productUnit_pair_zero (n : ℕ) (x : K F n) (u v : Additive Fˣ)
    (h : MilnorK.K2.symbolBilinear F u v = 0) :
    productUnit (n + 1) (productUnit n x u) v = 0 := by
  have hh : ((productUnit (n + 1)).flip v).comp ((productUnit n).flip u) = 0 := by
    apply linearMap_ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, productUnit_symbol,
      LinearMap.zero_apply]
    let b : SymbolTuple F (n + 1 + 1) := Fin.snoc (Fin.snoc a u.toMul) v.toMul
    let i : Fin (n + 1 + 1) := (Fin.last n).castSucc
    let j : Fin (n + 1 + 1) := Fin.last (n + 1)
    have hij : i.val + 1 = j.val := by simp [i, j]
    have hb : MilnorK.K2.symbol (b i) (b j) = 0 := by
      simp only [b, i, j, Fin.snoc_castSucc, Fin.snoc_last]
      exact h
    have hi := congrArg (adjacentPairMap b i j hij) hb
    simpa only [adjacentPairMap_symbol, Function.update_eq_self, map_zero] using hi
  exact LinearMap.congr_fun hh x

variable {L : Type u} {κ : Type v} [Field L] [Field κ]

open MilnorK.K2 in
/-- Specialization of an appended symbol is multiplication by its residue unit part. -/
theorem specialize_symbol_snoc (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (n : ℕ) (a : SymbolTuple L n) (b : Lˣ) :
    specialize d hd (n + 1) (symbol (Fin.snoc a b)) =
      productUnit n (specialize d hd n (symbol a)) (d.unitPart (Additive.ofMul b)) := by
  simp only [specialize_symbol, productUnit_symbol]
  congr 1
  exact Fin.comp_snoc (fun c : Lˣ => (d.unitPart (Additive.ofMul c)).toMul) a b

end MilnorK
