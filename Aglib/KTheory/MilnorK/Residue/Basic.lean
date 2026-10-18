/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.Algebra

/-!
# The sign-correct tame residue in every degree

The residue is constructed from the original discrete valuation/reduction data.
Its right-slot recursion retains the correction `r(a) - v(a){-1}`. In degree
one it is the integer valuation. In all higher degrees the recursion is
proved multilinear and Steinberg before descending to the actual quotient.
The convention places the uniformizer last.
-/

@[expose] public noncomputable section

namespace MilnorK

universe u v

variable {L : Type u} {κ : Type v} [Field L] [Field κ]

open MilnorK.K2 (DiscreteResidueData UnitReductionCompatible residueSign)

/-- The complete right-slot residue recursion, before descent. -/
def residueSymbol (d : DiscreteResidueData L κ) (hd : UnitReductionCompatible d) :
    (n : ℕ) → SymbolTuple L (n + 1) → K κ n
  | 0, a => d.value (Additive.ofMul (a 0)) • symbol Fin.elim0
  | n + 1, a => d.value (Additive.ofMul (a (Fin.last (n + 1)))) •
      specialize d hd (n + 1) (symbol (Fin.init a)) -
      productUnit n (residueSymbol d hd n (Fin.init a))
        (unitPartTwist d (residueSign κ) (Additive.ofMul (a (Fin.last (n + 1)))))

/-- The degree-one precursor is the valuation times the degree-zero generator. -/
@[simp] theorem residueSymbol_zero (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (a : SymbolTuple L 1) :
    residueSymbol d hd 0 a = d.value (Additive.ofMul (a 0)) • symbol Fin.elim0 := rfl

/-- The exact recursion on an appended tuple, including its residue-sign correction. -/
theorem residueSymbol_snoc (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (n : ℕ) (a : SymbolTuple L (n + 1)) (b : Lˣ) :
    residueSymbol d hd (n + 1) (Fin.snoc a b) =
      d.value (Additive.ofMul b) • specialize d hd (n + 1) (symbol a) -
        productUnit n (residueSymbol d hd n a)
          (unitPartTwist d (residueSign κ) (Additive.ofMul b)) := by
  simp only [residueSymbol, Fin.snoc_last, Fin.init_snoc]

/-- The full degree-two precursor agrees with the original signed tame formula. -/
theorem residueSymbol_one (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (a : SymbolTuple L 2) :
    residueSymbol d hd 1 a =
      unitsToOne κ (MilnorK.K2.rawTame d (Additive.ofMul (a 0)) (Additive.ofMul (a 1))) := by
  change d.value (Additive.ofMul (a 1)) • specialize d hd 1 (symbol (Fin.init a)) -
    productUnit 0 (d.value (Additive.ofMul (a 0)) • symbol Fin.elim0)
      (unitPartTwist d (residueSign κ) (Additive.ofMul (a 1))) = _
  rw [map_smul, LinearMap.smul_apply, productUnit_empty, specialize_symbol]
  have hs : symbol (fun i : Fin 1 => (d.unitPart (Additive.ofMul (Fin.init a i))).toMul) =
      unitsToOne κ (d.unitPart (Additive.ofMul (a 0))) := by
    congr 1
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  rw [hs]
  simp only [unitPartTwist_apply, MilnorK.K2.rawTame, map_add, map_sub, map_smul,
    smul_sub, smul_smul]
  abel

/-- Coordinatewise multiplicative additivity is proved for the complete recursion. -/
theorem residueSymbol_mul (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (n : ℕ) (a : SymbolTuple L (n + 1))
    (i : Fin (n + 1)) (b c : Lˣ) :
    residueSymbol d hd n (Function.update a i (b * c)) =
      residueSymbol d hd n (Function.update a i b) +
        residueSymbol d hd n (Function.update a i c) := by
  have hmul : Additive.ofMul (b * c) = Additive.ofMul b + Additive.ofMul c := rfl
  induction n with
  | zero =>
      have hi : i = 0 := Fin.ext (by omega)
      subst i
      simp only [residueSymbol_zero, Function.update_self, hmul, map_add,
        add_zsmul]
  | succ n ih =>
      cases i using Fin.lastCases with
      | last =>
          simp only [residueSymbol, Function.update_self, Fin.init_update_last,
            hmul, map_add, add_zsmul]
          abel
      | cast i =>
          have hne : Fin.last (n + 1) ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
          simp only [residueSymbol, Function.update_of_ne hne, Fin.init_update_castSucc,
            symbol_mul, map_add, ih, LinearMap.add_apply, smul_add]
          abel

/-- The two last slots of the recursion factor through the old tame and Steinberg maps. -/
theorem residueSymbol_snoc_snoc (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (n : ℕ) (a : SymbolTuple L (n + 1)) (b c : Lˣ) :
    residueSymbol d hd (n + 1 + 1) (Fin.snoc (Fin.snoc a b) c) =
      productUnit (n + 1) (specialize d hd (n + 1) (symbol a))
        (MilnorK.K2.rawTame d (Additive.ofMul b) (Additive.ofMul c)) +
      productUnit (n + 1)
        (productUnit n (residueSymbol d hd n a)
          (unitPartTwist d (residueSign κ) (Additive.ofMul b)))
        (unitPartTwist d (residueSign κ) (Additive.ofMul c)) := by
  rw [residueSymbol_snoc, residueSymbol_snoc, specialize_symbol_snoc]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [unitPartTwist_apply d (residueSign κ) (Additive.ofMul c)]
  simp only [MilnorK.K2.rawTame, map_add, map_sub, map_smul, smul_sub, smul_smul]
  abel

/-- A last-adjacent Steinberg pair vanishes, for every length of the preceding tuple. -/
theorem residueSymbol_last_steinberg (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (n : ℕ) (a : SymbolTuple L n) (b c : Lˣ)
    (hbc : (b : L) + (c : L) = 1) :
    residueSymbol d hd (n + 1) (Fin.snoc (Fin.snoc a b) c) = 0 := by
  cases n with
  | zero =>
      rw [residueSymbol_one]
      change unitsToOne κ (MilnorK.K2.rawTame d (Additive.ofMul b) (Additive.ofMul c)) = 0
      rw [MilnorK.K2.rawTame_steinberg d b c hbc, map_zero]
  | succ n =>
      rw [residueSymbol_snoc_snoc, MilnorK.K2.rawTame_steinberg d b c hbc, map_zero,
        zero_add]
      apply productUnit_pair_zero
      exact unitPartTwist_steinberg d hd (residueSign κ) b c hbc

/-- Every adjacent Steinberg pair is killed, with all remaining entries arbitrary. -/
theorem residueSymbol_steinberg (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (n : ℕ) (a : SymbolTuple L (n + 1))
    (i j : Fin (n + 1)) (hij : i.val + 1 = j.val)
    (hab : (a i : L) + (a j : L) = 1) : residueSymbol d hd n a = 0 := by
  induction n with
  | zero =>
      have hi := i.isLt
      have hj := j.isLt
      omega
  | succ n ih =>
      cases j using Fin.lastCases with
      | last =>
          have hi : i = (Fin.last n).castSucc := Fin.ext (by simpa using hij)
          have ha : Fin.snoc (Fin.snoc (Fin.init (Fin.init a)) (a i))
              (a (Fin.last (n + 1))) = a := by
            rw [hi]
            change Fin.snoc (Fin.snoc (Fin.init (Fin.init a)) ((Fin.init a) (Fin.last n)))
              (a (Fin.last (n + 1))) = a
            rw [Fin.snoc_init_self, Fin.snoc_init_self]
          have h := residueSymbol_last_steinberg d hd n (Fin.init (Fin.init a))
            (a i) (a (Fin.last (n + 1))) hab
          rwa [ha] at h
      | cast j =>
          cases i using Fin.lastCases with
          | last =>
              have hj := j.isLt
              simp only [Fin.val_last, Fin.val_castSucc] at hij
              omega
          | cast i =>
              have hrel : symbol (Fin.init a) = 0 := steinberg (Fin.init a) i j hij hab
              have hres := ih (Fin.init a) i j hij hab
              simp only [residueSymbol, hrel, hres, map_zero, smul_zero,
                LinearMap.zero_apply, sub_zero]

/-- The actual all-degree tame homomorphism, after all relations have been proved. -/
def residue (d : DiscreteResidueData L κ) (hd : UnitReductionCompatible d)
    (n : ℕ) : K L (n + 1) →ₗ[ℤ] K κ n :=
  lift (residueSymbol d hd n) ⟨residueSymbol_mul d hd n, residueSymbol_steinberg d hd n⟩

/-- On every symbol the descended residue is its full sign-correct recursion. -/
@[simp] theorem residue_symbol (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (n : ℕ) (a : SymbolTuple L (n + 1)) :
    residue d hd n (symbol a) = residueSymbol d hd n a := lift_symbol _ _ _

/-- The exact right-slot rule is available on all symbols, including entries with poles. -/
theorem residue_symbol_snoc (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (n : ℕ) (a : SymbolTuple L (n + 1)) (b : Lˣ) :
    residue d hd (n + 1) (symbol (Fin.snoc a b)) =
      d.value (Additive.ofMul b) • specialize d hd (n + 1) (symbol a) -
        productUnit n (residue d hd n (symbol a))
          (unitPartTwist d (residueSign κ) (Additive.ofMul b)) :=
  by
    simp only [residue_symbol]
    exact residueSymbol_snoc d hd n a b

/-- The degree-one residue is exactly the given integer valuation. -/
theorem zeroEquiv_residue (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (x : K L 1) :
    zeroEquiv κ (residue d hd 0 x) = d.value (oneEquiv L x) := by
  have h : (zeroEquiv κ).toLinearMap.comp (residue d hd 0) =
      d.value.comp (oneEquiv L).toLinearMap := by
    apply linearMap_ext
    intro a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, residue_symbol,
      residueSymbol_zero, map_smul, zeroEquiv_symbol, smul_eq_mul, mul_one]
    exact congrArg d.value (oneEquiv_symbol L a).symm
  exact LinearMap.congr_fun h x

/-- Every all-unit symbol has zero residue in every positive degree. -/
theorem residue_symbol_units (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (n : ℕ) (a : SymbolTuple L (n + 1))
    (ha : ∀ i, d.value (Additive.ofMul (a i)) = 0) : residue d hd n (symbol a) = 0 := by
  rw [residue_symbol]
  induction n with
  | zero => simp only [residueSymbol_zero, ha, zero_smul]
  | succ n ih =>
      have hu : ∀ i, d.value (Additive.ofMul (Fin.init a i)) = 0 := fun i => ha i.castSucc
      simp only [residueSymbol, ha, zero_smul, ih (Fin.init a) hu, map_zero,
        LinearMap.zero_apply, sub_zero]

/-- Last-slot uniformizer normalization, including the empty preceding tuple. -/
theorem residue_symbol_uniformizer (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (n : ℕ) (a : SymbolTuple L n)
    (ha : ∀ i, d.value (Additive.ofMul (a i)) = 0) :
    residue d hd n (symbol (Fin.snoc a d.uniformizer)) =
      symbol (fun i => (d.unitPart (Additive.ofMul (a i))).toMul) := by
  cases n with
  | zero =>
      rw [residue_symbol, residueSymbol_zero]
      change d.value (Additive.ofMul d.uniformizer) • symbol Fin.elim0 = _
      rw [d.value_uniformizer, one_smul]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n =>
      rw [residue_symbol_snoc, d.value_uniformizer, residue_symbol_units d hd n a ha,
        map_zero, LinearMap.zero_apply, sub_zero, one_smul, specialize_symbol]

/-- A principal-unit entry kills the residue even if all the other entries have poles. -/
theorem residue_symbol_principal (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (n : ℕ) (a : SymbolTuple L (n + 1))
    (i : Fin (n + 1)) (hv : d.value (Additive.ofMul (a i)) = 0)
    (hu : d.unitPart (Additive.ofMul (a i)) = 0) : residue d hd n (symbol a) = 0 := by
  rw [residue_symbol]
  induction n with
  | zero =>
      have hi : i = 0 := Fin.ext (by omega)
      subst i
      simp only [residueSymbol_zero, hv, zero_smul]
  | succ n ih =>
      cases i using Fin.lastCases with
      | last =>
          simp only [residueSymbol, hv, hu, unitPartTwist_apply, zero_smul, sub_self,
            map_zero]
      | cast i =>
          have hs : specialize d hd (n + 1) (symbol (Fin.init a)) = 0 := by
            rw [specialize_symbol]
            apply symbol_eq_zero_of_eq_one _ i
            change (d.unitPart (Additive.ofMul (a i.castSucc))).toMul = 1
            rw [hu]
            rfl
          have hr := ih (Fin.init a) i hv hu
          simp only [residueSymbol, hs, hr, smul_zero, map_zero, LinearMap.zero_apply,
            sub_zero]

/-- Repeated uniformizers retain the entire repeated minus-one symbol in the target. -/
theorem residue_symbol_uniformizers (d : DiscreteResidueData L κ)
    (hd : UnitReductionCompatible d) (n : ℕ) :
    residue d hd n (symbol (fun _ => d.uniformizer)) = symbol (fun _ => (-1 : κˣ)) := by
  rw [residue_symbol]
  induction n with
  | zero =>
      rw [residueSymbol_zero, d.value_uniformizer, one_smul]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      have hs : specialize d hd (n + 1) (symbol (fun _ => d.uniformizer)) = 0 :=
        specialize_symbol_uniformizer d hd (n + 1) (fun _ => d.uniformizer) 0 rfl
      change d.value (Additive.ofMul d.uniformizer) •
        specialize d hd (n + 1) (symbol (fun _ => d.uniformizer)) -
        productUnit n (residueSymbol d hd n (fun _ => d.uniformizer))
          (unitPartTwist d (residueSign κ) (Additive.ofMul d.uniformizer)) = _
      rw [hs, ih, unitPartTwist_apply, d.unitPart_uniformizer, d.value_uniformizer]
      simp only [smul_zero, one_smul, zero_sub, map_neg, neg_neg, productUnit_symbol]
      congr 1
      funext i
      cases i using Fin.lastCases <;> simp [residueSign]

end MilnorK
