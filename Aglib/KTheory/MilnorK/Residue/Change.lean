/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.Basic

/-!
# Change of normalized residue unit parts

For the original discrete valuation data, replacing the unit-part homomorphism
`r` by `r - v e` changes positive-degree specialization by right multiplication
of the residue by `-e`. The residue itself is unchanged when the valuation is
unchanged. The proof uses actual adjacent-pair maps and the Milnor identity
`{e,e} = -{-1,e}`; neither conclusion is assumed as a descent hypothesis.
-/

@[expose] public noncomputable section

namespace MilnorK

universe u v

variable {F : Type u} [Field F]

/-- Interchanging the last two unit factors negates the product on every class. -/
theorem productUnit_pair_skew (n : ℕ) (x : K F n) (u v : Additive Fˣ) :
    productUnit (n + 1) (productUnit n x u) v =
      -productUnit (n + 1) (productUnit n x v) u := by
  have h : ((productUnit (n + 1)).flip v).comp ((productUnit n).flip u) =
      -((productUnit (n + 1)).flip u).comp ((productUnit n).flip v) := by
    apply linearMap_ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.neg_apply,
      productUnit_symbol]
    let b : SymbolTuple F (n + 1 + 1) := Fin.snoc (Fin.snoc a u.toMul) v.toMul
    have hi := congrArg
      (adjacentPairMap b (Fin.last n).castSucc (Fin.last (n + 1)) (by simp))
      (MilnorK.K2.symbol_skew u.toMul v.toMul)
    simpa only [adjacentPairMap_symbol, map_neg, b, ← Fin.snoc_update,
      Fin.update_snoc_last] using hi
  exact LinearMap.congr_fun h x

/-- The diagonal last pair is the negative pair `(-1,e)`, with its prefix retained. -/
theorem productUnit_pair_self (n : ℕ) (x : K F n) (e : Additive Fˣ) :
    productUnit (n + 1) (productUnit n x e) e =
      -productUnit (n + 1) (productUnit n x (MilnorK.K2.residueSign F)) e := by
  have h : ((productUnit (n + 1)).flip e).comp ((productUnit n).flip e) =
      ((productUnit (n + 1)).flip (MilnorK.K2.residueSign F)).comp
        ((productUnit n).flip e) := by
    apply linearMap_ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, productUnit_symbol]
    let b : SymbolTuple F (n + 1 + 1) := Fin.snoc (Fin.snoc a e.toMul) e.toMul
    have hi := congrArg
      (adjacentPairMap b (Fin.last n).castSucc (Fin.last (n + 1)) (by simp))
      (MilnorK.K2.symbol_self e.toMul)
    simpa only [adjacentPairMap_symbol, b, ← Fin.snoc_update,
      Fin.update_snoc_last, MilnorK.K2.residueSign, toMul_ofMul] using hi
  exact (LinearMap.congr_fun h x).trans (productUnit_pair_skew n x e _)

variable {L : Type u} {κ : Type v} [Field L] [Field κ]

open MilnorK.K2 (DiscreteResidueData UnitReductionCompatible residueSign)

/-- Degree-zero specialization is independent of all choices of residue data. -/
theorem specialize_zero_eq (d d' : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (hd' : UnitReductionCompatible d') :
    specialize d' hd' 0 = specialize d hd 0 := by
  apply linearMap_ext
  intro a
  simp only [specialize_symbol]
  congr 1
  funext i
  exact Fin.elim0 i

/-- The exact positive-degree specialization change, on the actual quotient.
Only the unit-part change is needed; invariance of the valuation is used for
residue invariance below. -/
theorem specialize_change (d d' : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (hd' : UnitReductionCompatible d')
    (e : Additive κˣ)
    (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e) (n : ℕ) :
    specialize d' hd' (n + 1) = specialize d hd (n + 1) -
      ((productUnit n).flip e).comp (residue d hd n) := by
  induction n with
  | zero =>
      apply linearMap_ext
      intro a
      have ha : a = fun _ => a 0 := funext (fun i => congrArg a (Fin.ext (by omega)))
      rw [ha]
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.flip_apply,
        specialize_symbol, residue_symbol, residueSymbol_zero, map_smul, productUnit_empty]
      change unitsToOne κ (d'.unitPart (Additive.ofMul (a 0))) =
        unitsToOne κ (d.unitPart (Additive.ofMul (a 0))) -
          d.value (Additive.ofMul (a 0)) • unitsToOne κ e
      rw [hunit, map_sub, map_smul]
  | succ n ih =>
      apply linearMap_ext
      intro a
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.flip_apply]
      rw [← Fin.snoc_init_self a, specialize_symbol_snoc, specialize_symbol_snoc,
        residue_symbol_snoc]
      have hi := LinearMap.congr_fun ih (symbol (Fin.init a))
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.flip_apply] at hi
      rw [hi, hunit]
      simp only [unitPartTwist_apply, map_sub, map_smul, LinearMap.sub_apply,
        LinearMap.smul_apply]
      rw [productUnit_pair_skew n (residue d hd n (symbol (Fin.init a))) e
        (d.unitPart (Additive.ofMul (a (Fin.last (n + 1))))),
        productUnit_pair_self]
      module

/-- The specialization correction evaluated on an arbitrary positive-degree class. -/
theorem specialize_change_apply (d d' : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (hd' : UnitReductionCompatible d')
    (e : Additive κˣ)
    (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e)
    (n : ℕ) (x : K L (n + 1)) :
    specialize d' hd' (n + 1) x = specialize d hd (n + 1) x -
      productUnit n (residue d hd n x) e :=
  LinearMap.congr_fun (specialize_change d d' hd hd' e hunit n) x

/-- Changing normalized residue unit parts leaves every constructed residue unchanged. -/
theorem residue_eq_of_unitPart_change (d d' : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (hd' : UnitReductionCompatible d')
    (e : Additive κˣ)
    (hvalue : ∀ a, d'.value a = d.value a)
    (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e) (n : ℕ) :
    residue d' hd' n = residue d hd n := by
  induction n with
  | zero =>
      apply linearMap_ext
      intro a
      simp only [residue_symbol, residueSymbol_zero, hvalue]
  | succ n ih =>
      apply linearMap_ext
      intro a
      rw [← Fin.snoc_init_self a, residue_symbol_snoc, residue_symbol_snoc,
        specialize_change_apply d d' hd hd' e hunit n, ih]
      simp only [unitPartTwist_apply, hunit, hvalue, map_sub, map_smul, smul_sub]
      abel

/-- The actual residue kernels are identical under compatible changes of unit parts. -/
theorem residue_kernel_eq_of_unitPart_change (d d' : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (hd' : UnitReductionCompatible d')
    (e : Additive κˣ)
    (hvalue : ∀ a, d'.value a = d.value a)
    (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e) (n : ℕ) :
    (residue d' hd' n).ker = (residue d hd n).ker :=
  congrArg LinearMap.ker (residue_eq_of_unitPart_change d d' hd hd' e hvalue hunit n)

/-- Specializations agree on the residue kernel, in every positive degree. -/
theorem specialize_eq_on_residue_kernel (d d' : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (hd' : UnitReductionCompatible d')
    (e : Additive κˣ)
    (hunit : ∀ a, d'.unitPart a = d.unitPart a - d.value a • e)
    (n : ℕ) (x : K L (n + 1)) (hx : residue d hd n x = 0) :
    specialize d' hd' (n + 1) x = specialize d hd (n + 1) x := by
  rw [specialize_change_apply d d' hd hd' e hunit, hx, map_zero,
    LinearMap.zero_apply, sub_zero]

end MilnorK
