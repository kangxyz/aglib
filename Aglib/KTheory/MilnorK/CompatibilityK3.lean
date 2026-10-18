/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.CompatibilityK2
public import Aglib.KTheory.MilnorK.K3.Map
public import Mathlib.Tactic.FinCases

/-!
# Compatibility with the existing degree-three nested tensor quotient

The degree-three part of the all-degree presentation is explicitly equivalent
to `MilnorK3.K3`. The map from the old quotient first descends the last two
coordinates through actual old K₂, then descends the first coordinate and its
Steinberg relation through actual old K₃. The reverse map respects both
adjacent Steinberg relations. Both inverse identities and field naturality
are proved on symbols, using the already proved universal properties.
-/

@[expose] public section

noncomputable section

namespace MilnorK

universe u v

variable {F : Type u} [Field F]

/-- Updating the first coordinate of a triple. -/
private theorem triple_update_zero (a b c d : Fˣ) :
    Function.update ![a, b, c] 0 d = ![d, b, c] := by
  funext i
  fin_cases i <;> simp

/-- Updating the middle coordinate of a triple. -/
private theorem triple_update_one (a b c d : Fˣ) :
    Function.update ![a, b, c] 1 d = ![a, d, c] := by
  funext i
  fin_cases i <;> simp

/-- Updating the final coordinate of a triple. -/
private theorem triple_update_two (a b c d : Fˣ) :
    Function.update ![a, b, c] 2 d = ![a, b, d] := by
  funext i
  fin_cases i <;> simp

/-- Triple symbols are multiplicatively additive in the first coordinate. -/
theorem tripleSymbol_mul_left (a a' b c : Fˣ) :
    symbol ![a * a', b, c] = symbol ![a, b, c] + symbol ![a', b, c] := by
  simpa only [triple_update_zero] using symbol_mul ![a, b, c] 0 a a'

/-- Triple symbols are multiplicatively additive in the middle coordinate. -/
theorem tripleSymbol_mul_middle (a b b' c : Fˣ) :
    symbol ![a, b * b', c] = symbol ![a, b, c] + symbol ![a, b', c] := by
  simpa only [triple_update_one] using symbol_mul ![a, b, c] 1 b b'

/-- Triple symbols are multiplicatively additive in the final coordinate. -/
theorem tripleSymbol_mul_right (a b c c' : Fˣ) :
    symbol ![a, b, c * c'] = symbol ![a, b, c] + symbol ![a, b, c'] := by
  simpa only [triple_update_two] using symbol_mul ![a, b, c] 2 c c'

variable (F)

/-- With the first coordinate fixed, the remaining two coordinates are bilinear. -/
def tripleTailBilinear (a : Fˣ) : Additive Fˣ →ₗ[ℤ] Additive Fˣ →ₗ[ℤ] K F 3 :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun b => AddMonoidHom.toIntLinearMap {
      toFun := fun c => symbol ![a, b.toMul, c.toMul]
      map_zero' := symbol_eq_zero_of_eq_one _ 2 rfl
      map_add' := fun c d => tripleSymbol_mul_right a b.toMul c.toMul d.toMul }
    map_zero' := by
      apply LinearMap.ext
      intro c
      exact symbol_eq_zero_of_eq_one _ 1 rfl
    map_add' := by
      intro b c
      apply LinearMap.ext
      intro d
      exact tripleSymbol_mul_middle a b.toMul c.toMul d.toMul }

/-- The fixed-first-coordinate triple symbol descends through the original K₂ quotient. -/
def tripleTailToNew (a : Fˣ) : MilnorK.K2.Group F →ₗ[ℤ] K F 3 :=
  MilnorK.K2.lift (tripleTailBilinear F a)
    (fun b c h => steinberg ![a, b, c] 1 2 rfl h)

/-- The last-two-coordinate descent preserves the literal ordered triple. -/
@[simp] theorem tripleTailToNew_symbol (a b c : Fˣ) :
    tripleTailToNew F a (MilnorK.K2.symbol b c) = symbol ![a, b, c] := rfl

/-- The already-descended tail is bilinear in the first unit and the original K₂ class. -/
def tripleFirstBilinear : Additive Fˣ →ₗ[ℤ] MilnorK.K2.Group F →ₗ[ℤ] K F 3 :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun a => tripleTailToNew F a.toMul
    map_zero' := by
      apply MilnorK.K2.linearMap_ext
      intro b c
      exact symbol_eq_zero_of_eq_one _ 0 rfl
    map_add' := by
      intro a b
      apply MilnorK.K2.linearMap_ext
      intro c d
      exact tripleSymbol_mul_left a.toMul b.toMul c d }

/-- The old nested tensor quotient maps into the all-degree presentation. -/
def fromOldK3 : MilnorK.K3.Group F →ₗ[ℤ] K F 3 :=
  MilnorK.K3.lift (tripleFirstBilinear F)
    (fun a b c h => steinberg ![a, b, c] 0 1 rfl h)

/-- The comparison from the old degree-three group preserves ordered triple symbols. -/
@[simp] theorem fromOldK3_symbol (a b c : Fˣ) :
    fromOldK3 F (MilnorK.K3.symbol3 a b c) = symbol ![a, b, c] := rfl

/-- The all-degree presentation maps back to the original nested degree-three quotient. -/
def toOldK3 : K F 3 →ₗ[ℤ] MilnorK.K3.Group F :=
  lift (fun a => MilnorK.K3.symbol3 (a 0) (a 1) (a 2)) {
    map_mul := by
      intro a i b c
      fin_cases i <;> simp [MilnorK.K3.symbol3_mul_left, MilnorK.K3.symbol3_mul_middle,
        MilnorK.K3.symbol3_mul_right]
    steinberg := by
      intro a i j hij h
      fin_cases i <;> fin_cases j <;>
        simp_all [MilnorK.K3.symbol3_steinberg_left, MilnorK.K3.symbol3_steinberg_right] }

/-- The reverse comparison is exactly the old symbol of the three coordinates. -/
@[simp] theorem toOldK3_symbol (a : SymbolTuple F 3) :
    toOldK3 F (symbol a) = MilnorK.K3.symbol3 (a 0) (a 1) (a 2) := by
  simp [toOldK3]

/-- The all-degree Milnor group agrees with the existing nested degree-three quotient. -/
def threeEquiv : K F 3 ≃ₗ[ℤ] MilnorK.K3.Group F :=
  LinearEquiv.ofLinearMap (toOldK3 F) (fromOldK3 F) (by
    apply MilnorK.K3.linearMap_ext
    intro a b c
    simp) (by
    apply linearMap_ext
    intro a
    simp only [LinearMap.comp_apply, toOldK3_symbol, fromOldK3_symbol, LinearMap.id_apply]
    congr 1
    funext i
    fin_cases i <;> rfl)

/-- The degree-three equivalence has the standard ordered triple normalization. -/
@[simp] theorem threeEquiv_symbol (a : SymbolTuple F 3) :
    threeEquiv F (symbol a) = MilnorK.K3.symbol3 (a 0) (a 1) (a 2) := toOldK3_symbol F a

/-- The inverse equivalence sends each old triple symbol to its ordered tuple. -/
@[simp] theorem threeEquiv_symm_symbol (a b c : Fˣ) :
    (threeEquiv F).symm (MilnorK.K3.symbol3 a b c) = symbol ![a, b, c] := rfl

variable {F} {E : Type v} [Field E]

/-- The degree-three equivalence commutes with the original and all-degree field maps. -/
theorem threeEquiv_map (f : F →+* E) (x : K F 3) :
    threeEquiv E (map 3 f x) = MilnorK.K3.map f (threeEquiv F x) := by
  have h : (threeEquiv E).toLinearMap.comp (map 3 f) =
      (MilnorK.K3.map f).comp (threeEquiv F).toLinearMap := by
    apply linearMap_ext
    intro a
    simp [MilnorK.K3.map_symbol3]
  exact LinearMap.congr_fun h x

end MilnorK
