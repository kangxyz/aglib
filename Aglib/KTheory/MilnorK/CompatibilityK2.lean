/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Map
public import Aglib.KTheory.MilnorK.K2.Map
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Compatibility with the existing degree-two tensor quotient

The standard all-degree symbol presentation in degree two is explicitly
isomorphic to the existing `MilnorK2.K2`. Both directions send each ordered
pair to the same symbol. Their inverse identities use the actual universal
properties on each side. The equivalence is natural under field maps.
-/

@[expose] public section

noncomputable section

namespace MilnorK

universe u v

variable {F : Type u} [Field F]

/-- Updating the first coordinate of a two-entry tuple. -/
private theorem pair_update_zero (a b c : Fˣ) : Function.update ![a, b] 0 c = ![c, b] := by
  funext i
  fin_cases i <;> simp

/-- Updating the second coordinate of a two-entry tuple. -/
private theorem pair_update_one (a b c : Fˣ) : Function.update ![a, b] 1 c = ![a, c] := by
  funext i
  fin_cases i <;> simp

/-- The two-entry symbol is multiplicatively additive in its first coordinate. -/
theorem pairSymbol_mul_left (a b c : Fˣ) :
    symbol ![a * b, c] = symbol ![a, c] + symbol ![b, c] := by
  simpa only [pair_update_zero] using symbol_mul ![a, c] 0 a b

/-- The two-entry symbol is multiplicatively additive in its second coordinate. -/
theorem pairSymbol_mul_right (a b c : Fˣ) :
    symbol ![a, b * c] = symbol ![a, b] + symbol ![a, c] := by
  simpa only [pair_update_one] using symbol_mul ![a, b] 1 b c

variable (F)

/-- The genuine bilinear pair-symbol map in the all-degree presentation. -/
def pairSymbolBilinear : Additive Fˣ →ₗ[ℤ] Additive Fˣ →ₗ[ℤ] K F 2 :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun a => AddMonoidHom.toIntLinearMap {
      toFun := fun b => symbol ![a.toMul, b.toMul]
      map_zero' := symbol_eq_zero_of_eq_one _ 1 rfl
      map_add' := fun b c => pairSymbol_mul_right a.toMul b.toMul c.toMul }
    map_zero' := by
      apply LinearMap.ext
      intro b
      exact symbol_eq_zero_of_eq_one _ 0 rfl
    map_add' := by
      intro a b
      apply LinearMap.ext
      intro c
      exact pairSymbol_mul_left a.toMul b.toMul c.toMul }

/-- The bilinear pair-symbol map evaluates to the ordered two-entry symbol. -/
@[simp] theorem pairSymbolBilinear_apply (a b : Fˣ) :
    pairSymbolBilinear F (Additive.ofMul a) (Additive.ofMul b) = symbol ![a, b] := rfl

/-- The old tensor quotient maps to the all-degree presentation in degree two. -/
def fromOldK2 : MilnorK.K2.Group F →ₗ[ℤ] K F 2 :=
  MilnorK.K2.lift (pairSymbolBilinear F) (fun a b h => steinberg ![a, b] 0 1 rfl h)

/-- The comparison from the old quotient preserves the actual pair symbols. -/
@[simp] theorem fromOldK2_symbol (a b : Fˣ) :
    fromOldK2 F (MilnorK.K2.symbol a b) = symbol ![a, b] := rfl

/-- The all-degree presentation maps back to the old degree-two tensor quotient. -/
def toOldK2 : K F 2 →ₗ[ℤ] MilnorK.K2.Group F :=
  lift (fun a => MilnorK.K2.symbol (a 0) (a 1)) {
    map_mul := by
      intro a i b c
      fin_cases i <;> simp [MilnorK.K2.symbol_mul_left, MilnorK.K2.symbol_mul_right]
    steinberg := by
      intro a i j hij h
      fin_cases i <;> fin_cases j <;> simp_all [MilnorK.K2.steinberg] }

/-- The reverse comparison evaluates every tuple by the original ordered symbol. -/
@[simp] theorem toOldK2_symbol (a : SymbolTuple F 2) :
    toOldK2 F (symbol a) = MilnorK.K2.symbol (a 0) (a 1) := by
  simp [toOldK2]

/-- The all-degree Milnor group agrees with the existing degree-two tensor quotient. -/
def twoEquiv : K F 2 ≃ₗ[ℤ] MilnorK.K2.Group F :=
  LinearEquiv.ofLinearMap (toOldK2 F) (fromOldK2 F) (by
    apply MilnorK.K2.linearMap_ext
    intro a b
    simp) (by
    apply linearMap_ext
    intro a
    simp only [LinearMap.comp_apply, toOldK2_symbol, fromOldK2_symbol, LinearMap.id_apply]
    congr 1
    funext i
    fin_cases i <;> rfl)

/-- The degree-two equivalence has the expected ordered symbol normalization. -/
@[simp] theorem twoEquiv_symbol (a : SymbolTuple F 2) :
    twoEquiv F (symbol a) = MilnorK.K2.symbol (a 0) (a 1) := toOldK2_symbol F a

/-- The inverse degree-two equivalence sends each old symbol to its ordered tuple. -/
@[simp] theorem twoEquiv_symm_symbol (a b : Fˣ) :
    (twoEquiv F).symm (MilnorK.K2.symbol a b) = symbol ![a, b] := rfl

variable {F} {E : Type v} [Field E]

/-- The degree-two comparison is natural for the actual old and new field maps. -/
theorem twoEquiv_map (f : F →+* E) (x : K F 2) :
    twoEquiv E (map 2 f x) = MilnorK.K2.map f (twoEquiv F x) := by
  have h : (twoEquiv E).toLinearMap.comp (map 2 f) =
      (MilnorK.K2.map f).comp (twoEquiv F).toLinearMap := by
    apply linearMap_ext
    intro a
    simp
  exact LinearMap.congr_fun h x

end MilnorK
