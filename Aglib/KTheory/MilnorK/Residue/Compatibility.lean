/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.Basic
public import Aglib.KTheory.MilnorK.CompatibilityK3

/-!
# Compatibility of general residues with the existing low-degree maps

The general residue is compared with the actual old tame map in degree two
and the actual old `residue3` in degree three on every quotient class. The
latter comparison uses the full recursive formula, old skew symmetry and
old cyclicity; no uniqueness premise from normalized symbols is imposed.
-/

@[expose] public noncomputable section

namespace MilnorK

universe u v

variable {F : Type u} [Field F]

/-- The degree-one right-unit product is exactly the original K₂ bilinear symbol. -/
theorem twoEquiv_productUnit (x : K F 1) (b : Additive Fˣ) :
    twoEquiv F (productUnit 1 x b) = MilnorK.K2.symbolBilinear F (oneEquiv F x) b := by
  have h : (twoEquiv F).toLinearMap.comp ((productUnit 1).flip b) =
      ((MilnorK.K2.symbolBilinear F).flip b).comp (oneEquiv F).toLinearMap := by
    apply linearMap_ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, LinearEquiv.coe_coe,
      productUnit_symbol, twoEquiv_symbol, oneEquiv_symbol]
    rfl
  exact LinearMap.congr_fun h x

variable {L : Type u} {κ : Type v} [Field L] [Field κ]

open MilnorK.K2 (DiscreteResidueData UnitReductionCompatible residueSign)

/-- Degree two agrees with the original tame homomorphism on all Milnor classes. -/
theorem oneEquiv_residue_one (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (x : K L 2) :
    oneEquiv κ (residue d hd 1 x) = MilnorK.K2.tame d (twoEquiv L x) := by
  have h : (oneEquiv κ).toLinearMap.comp (residue d hd 1) =
      (MilnorK.K2.tame d).comp (twoEquiv L).toLinearMap := by
    apply linearMap_ext
    intro a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, residue_symbol, residueSymbol_one]
    rw [twoEquiv_symbol, MilnorK.K2.tame_symbol]
    exact (oneEquiv κ).apply_symm_apply _
  exact LinearMap.congr_fun h x

/-- The complete degree-three symbol formula is the original cyclic residue. -/
theorem twoEquiv_residue_symbol_two (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (a : SymbolTuple L 3) :
    twoEquiv κ (residue d hd 2 (symbol a)) =
      MilnorK.K3.residue3 d hd (MilnorK.K3.symbol3 (a 0) (a 1) (a 2)) := by
  rw [residue_symbol]
  change twoEquiv κ (d.value (Additive.ofMul (a 2)) •
      specialize d hd 2 (symbol (Fin.init a)) -
      productUnit 1 (residueSymbol d hd 1 (Fin.init a))
        (unitPartTwist d (residueSign κ) (Additive.ofMul (a 2)))) = _
  rw [map_sub, map_smul, twoEquiv_specialize, twoEquiv_productUnit, residueSymbol_one]
  have hunit : ∀ z : Additive κˣ, oneEquiv κ (unitsToOne κ z) = z :=
    (oneEquiv κ).apply_symm_apply
  rw [hunit, twoEquiv_symbol, MilnorK.K2.specialize_symbol]
  rw [MilnorK.K3.residue3_cyclic, MilnorK.K3.residue3_symbol,
    MilnorK.K3.residue3Bilinear_apply, MilnorK.K2.specialize_symbol, MilnorK.K2.tame_symbol]
  rw [MilnorK.K2.bilinear_symbol_skew, sub_neg_eq_add]
  rfl

/-- Degree three agrees with the original residue on every quotient class. -/
theorem twoEquiv_residue_two (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (x : K L 3) :
    twoEquiv κ (residue d hd 2 x) = MilnorK.K3.residue3 d hd (threeEquiv L x) := by
  have h : (twoEquiv κ).toLinearMap.comp (residue d hd 2) =
      (MilnorK.K3.residue3 d hd).comp (threeEquiv L).toLinearMap := by
    apply linearMap_ext
    intro a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [threeEquiv_symbol]
    exact twoEquiv_residue_symbol_two d hd a
  exact LinearMap.congr_fun h x

end MilnorK
