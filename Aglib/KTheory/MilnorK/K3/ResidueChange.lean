/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.Residue

/-!
# Independence of the degree-three residue from residue unit parts

The actual degree-three residue is unchanged when the value map is fixed and
the unit-part map changes by a valuation multiple. The proof uses the existing
degree-two tame invariance and specialization-change theorems: their two
correction terms cancel by Milnor skew symmetry.

Both elementary reduction-compatibility hypotheses remain explicit. This
generic algebraic result makes no concrete DVR or finite-extension norm claim.
-/

@[expose] public section

namespace MilnorK.K3

open MilnorK.K2

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A]

/-- Linear maps on the actual nested degree-three quotient are determined by symbols. -/
@[ext] theorem linearMap_ext (f g : Group K →ₗ[ℤ] A)
    (h : ∀ a b c : Kˣ, f (symbol3 a b c) = g (symbol3 a b c)) : f = g := by
  apply Submodule.linearMap_qext
  apply TensorProduct.ext'
  intro a x
  have hx :
      (f.comp (R3 K).mkQ).comp (TensorProduct.mk ℤ (UnitsAdd K) (MilnorK.K2.Group K) a) =
        (g.comp (R3 K).mkQ).comp (TensorProduct.mk ℤ (UnitsAdd K) (MilnorK.K2.Group K) a) := by
    apply MilnorK.K2.linearMap_ext
    intro b c
    exact h a.toMul b c
  exact LinearMap.congr_fun hx x

variable {k : Type*} [Field k]

/-- The two degree-two change corrections cancel in the bilinear residue precursor. -/
theorem residue3Bilinear_eq_of_unitPart_change (d d' : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (hd' : UnitReductionCompatible d') (e : UnitsAdd k)
    (hvalue : ∀ a, d'.value a = d.value a)
    (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e) :
    residue3Bilinear d' hd' = residue3Bilinear d hd := by
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro x
  have ht := tame_eq_of_unitPart_change d d' e hvalue hunit
  have hs := LinearMap.congr_fun (specialize_change d d' hd hd' e hunit) x
  change specialize d' hd' x =
    specialize d hd x - symbolBilinear k (tame d x) e at hs
  have hshift : d.unitPart a - d.value a • e - d.value a • residueSign k =
      (d.unitPart a - d.value a • residueSign k) - d.value a • e := by abel
  rw [residue3Bilinear_apply, residue3Bilinear_apply, hvalue, hunit, ht, hs, hshift]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, zsmul_sub]
  rw [bilinear_symbol_skew (tame d x) e]
  simp only [smul_neg, sub_neg_eq_add]
  abel

/-- Changing the unit-part decomposition preserves the actual descended K₃ residue. -/
theorem residue3_eq_of_unitPart_change (d d' : DiscreteResidueData K k)
    (hd : UnitReductionCompatible d) (hd' : UnitReductionCompatible d') (e : UnitsAdd k)
    (hvalue : ∀ a, d'.value a = d.value a)
    (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e) :
    residue3 d' hd' = residue3 d hd := by
  apply linearMap_ext
  intro a b c
  simp only [residue3_symbol, residue3Bilinear_eq_of_unitPart_change d d' hd hd' e hvalue hunit]

end MilnorK.K3
