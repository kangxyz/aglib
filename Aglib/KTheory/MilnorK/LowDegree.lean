/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Map

/-!
# The zeroth and first Milnor groups

The all-degree presentation gives `K F 0 ≃ₗ[ℤ] ℤ` and
`K F 1 ≃ₗ[ℤ] Additive Fˣ`. Both are explicit inverse maps with the
usual symbol normalization. These statements hold for every field and are
natural under arbitrary field homomorphisms.
-/

@[expose] public section

noncomputable section

namespace MilnorK

universe u v

variable (F : Type u) [Field F]

/-- The degree-zero symbol sends the empty tuple to the integer one. -/
def zeroToInt : K F 0 →ₗ[ℤ] ℤ :=
  lift (fun _ => 1) {
    map_mul := fun _ i => Fin.elim0 i
    steinberg := fun _ i => Fin.elim0 i }

/-- The integer multiple of the unique empty symbol. -/
def intToZero : ℤ →ₗ[ℤ] K F 0 :=
  (LinearMap.id : ℤ →ₗ[ℤ] ℤ).smulRight (symbol Fin.elim0)

/-- The degree-zero group is canonically the integers. -/
def zeroEquiv : K F 0 ≃ₗ[ℤ] ℤ :=
  LinearEquiv.ofLinearMap (zeroToInt F) (intToZero F) (by
    apply LinearMap.ext
    intro z
    simp [zeroToInt, intToZero]) (by
    apply linearMap_ext
    intro a
    have ha : a = Fin.elim0 := funext (fun i => Fin.elim0 i)
    subst a
    simp [zeroToInt, intToZero])

/-- The empty symbol has degree-zero value one. -/
@[simp] theorem zeroEquiv_symbol (a : SymbolTuple F 0) : zeroEquiv F (symbol a) = 1 :=
  by simp [zeroEquiv, zeroToInt]

/-- The inverse degree-zero equivalence sends integers to multiples of the empty symbol. -/
@[simp] theorem zeroEquiv_symm_apply (z : ℤ) :
    (zeroEquiv F).symm z = z • symbol Fin.elim0 := rfl

/-- The degree-one evaluation sends a single-entry symbol to that unit. -/
def oneToUnits : K F 1 →ₗ[ℤ] Additive Fˣ :=
  lift (fun a => Additive.ofMul (a 0)) {
    map_mul := by
      intro a i b c
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp
    steinberg := by
      intro a i j hij h
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      simp only [hi, hj, Fin.val_zero, zero_add, one_ne_zero] at hij }

/-- A unit defines its one-entry symbol; multiplicativity is the defining relation. -/
def unitsToOne : Additive Fˣ →ₗ[ℤ] K F 1 :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun a => symbol (fun _ => a.toMul)
    map_zero' := by
      exact symbol_eq_zero_of_eq_one _ 0 rfl
    map_add' := by
      intro a b
      change symbol (fun _ => a.toMul * b.toMul) =
        symbol (fun _ => a.toMul) + symbol (fun _ => b.toMul)
      have hup (c : Fˣ) : Function.update (fun _ : Fin 1 => a.toMul) 0 c =
          (fun _ => c) := by
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simp
      simpa only [hup] using symbol_mul (fun _ : Fin 1 => a.toMul) 0 a.toMul b.toMul }

/-- The degree-one group is canonically the multiplicative unit group, written additively. -/
def oneEquiv : K F 1 ≃ₗ[ℤ] Additive Fˣ :=
  LinearEquiv.ofLinearMap (oneToUnits F) (unitsToOne F) (by
    apply LinearMap.ext
    intro a
    simp [oneToUnits, unitsToOne]) (by
    apply linearMap_ext
    intro a
    change unitsToOne F (oneToUnits F (symbol a)) = symbol a
    rw [oneToUnits, lift_symbol]
    change symbol (fun _ => a 0) = symbol a
    congr 1
    funext i
    exact congrArg a (Subsingleton.elim 0 i))

/-- The degree-one equivalence has the standard symbol normalization. -/
@[simp] theorem oneEquiv_symbol (a : SymbolTuple F 1) :
    oneEquiv F (symbol a) = Additive.ofMul (a 0) := by
  simp [oneEquiv, oneToUnits]

/-- The inverse degree-one equivalence is the ordinary singleton symbol. -/
@[simp] theorem oneEquiv_symm_apply (a : Additive Fˣ) :
    (oneEquiv F).symm a = symbol (fun _ => a.toMul) := rfl

variable {F} {E : Type v} [Field E]

/-- Degree-zero field functoriality becomes the identity on the integers. -/
theorem zeroEquiv_map (f : F →+* E) (x : K F 0) :
    zeroEquiv E (map 0 f x) = zeroEquiv F x := by
  have h : (zeroEquiv E).toLinearMap.comp (map 0 f) = (zeroEquiv F).toLinearMap := by
    apply linearMap_ext
    intro a
    simp
  exact LinearMap.congr_fun h x

/-- Degree-one field functoriality becomes the usual map of multiplicative units. -/
theorem oneEquiv_map (f : F →+* E) (x : K F 1) :
    oneEquiv E (map 1 f x) =
      Additive.ofMul (Units.map f.toMonoidHom (oneEquiv F x).toMul) := by
  let uf : Additive Fˣ →ₗ[ℤ] Additive Eˣ :=
    (Units.map f.toMonoidHom).toAdditive.toIntLinearMap
  have h : (oneEquiv E).toLinearMap.comp (map 1 f) =
      uf.comp (oneEquiv F).toLinearMap := by
    apply linearMap_ext
    intro a
    simp [uf]
  exact LinearMap.congr_fun h x

end MilnorK
