/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Symbols

/-!
# Sign and Steinberg identities at arbitrary distinct coordinates

A bounded induction on the distance between two coordinates expresses their
transposition as three shorter transpositions. Adjacent skew symmetry then
implies skew symmetry at arbitrary distinct coordinates. Consequently a
Steinberg pair can be brought to adjacent coordinates, so arbitrary pair
insertion descends through the genuine degree-two Milnor quotient.

No alternating or repeated-entry-zero relation is imposed. Repeated entries
retain the usual contribution with a `-1` entry, in every characteristic.
-/

@[expose] public section

noncomputable section

namespace MilnorK

universe u

variable {F : Type u} [Field F] {n : ℕ}

private def swapTuple (a : SymbolTuple F n) (i j : Fin n) : SymbolTuple F n :=
  Function.update (Function.update a i (a j)) j (a i)

private theorem swapTuple_comm (a : SymbolTuple F n) (i j : Fin n) (hij : i ≠ j) :
    swapTuple a i j = swapTuple a j i := by
  exact Function.update_comm hij _ _ _

private theorem swapTuple_three (a : SymbolTuple F n) (i k j : Fin n)
    (hik : i ≠ k) (hij : i ≠ j) (hkj : k ≠ j) :
    swapTuple (swapTuple (swapTuple a i k) k j) i k = swapTuple a i j := by
  funext l
  by_cases hli : l = i
  · subst l
    simp [swapTuple, hik, hij, hkj, Ne.symm hij, Ne.symm hkj]
  by_cases hlk : l = k
  · subst l
    simp [swapTuple, hik, hij, hkj, Ne.symm hik, Ne.symm hij, Ne.symm hkj]
  by_cases hlj : l = j
  · subst l
    simp [swapTuple, hik, hij, hkj, Ne.symm hij, Ne.symm hkj]
  simp [swapTuple, hli, hlk, hlj]

private theorem symbol_skew_gap (d : ℕ) :
    ∀ (a : SymbolTuple F n) (i j : Fin n), i.val < j.val → j.val - i.val = d →
      symbol a = -symbol (swapTuple a i j) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a i j hij hd
    by_cases hadj : i.val + 1 = j.val
    · exact symbol_adjacent_skew a i j hadj
    let k : Fin n := ⟨i.val + 1, by omega⟩
    have hik : i ≠ k := by intro h; have := congrArg Fin.val h; dsimp [k] at this; omega
    have hij' : i ≠ j := by intro h; subst j; omega
    have hkj : k ≠ j := by intro h; have := congrArg Fin.val h; exact hadj this
    have h₁ : symbol a = -symbol (swapTuple a i k) :=
      symbol_adjacent_skew a i k rfl
    have h₂ : symbol (swapTuple a i k) =
        -symbol (swapTuple (swapTuple a i k) k j) :=
      ih (j.val - k.val) (by dsimp [k]; omega) (swapTuple a i k) k j
        (by dsimp [k]; omega) rfl
    have h₃ : symbol (swapTuple (swapTuple a i k) k j) =
        -symbol (swapTuple (swapTuple (swapTuple a i k) k j) i k) :=
      symbol_adjacent_skew _ i k rfl
    calc
      symbol a = -symbol (swapTuple a i k) := h₁
      _ = symbol (swapTuple (swapTuple a i k) k j) := by rw [h₂, neg_neg]
      _ = -symbol (swapTuple (swapTuple (swapTuple a i k) k j) i k) := h₃
      _ = -symbol (swapTuple a i j) := by rw [swapTuple_three a i k j hik hij' hkj]

/-- Interchanging any two distinct coordinates negates a Milnor symbol. -/
theorem symbol_skew (a : SymbolTuple F n) (i j : Fin n) (hij : i ≠ j) :
    symbol a = -symbol (Function.update (Function.update a i (a j)) j (a i)) := by
  by_cases hlt : i.val < j.val
  · exact symbol_skew_gap (j.val - i.val) a i j hlt rfl
  · have hgt : j.val < i.val := by
      have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
      omega
    have h := symbol_skew_gap (i.val - j.val) a j i hgt rfl
    rw [← swapTuple_comm a i j hij] at h
    exact h

/-- Skew symmetry with arbitrary substituted entries at distinct coordinates. -/
theorem symbol_update_skew (a : SymbolTuple F n) (i j : Fin n) (hij : i ≠ j)
    (b c : Fˣ) :
    symbol (Function.update (Function.update a i b) j c) =
      -symbol (Function.update (Function.update a i c) j b) := by
  have h := symbol_skew (Function.update (Function.update a i b) j c) i j hij
  rw [h]
  congr 2
  funext l
  by_cases hli : l = i
  · subst l
    simp [hij]
  by_cases hlj : l = j
  · subst l
    simp [hij]
  simp [hli, hlj]

/-- A Steinberg pair vanishes at any two distinct positions. -/
theorem steinberg_of_ne (a : SymbolTuple F n) (i j : Fin n) (hij : i ≠ j)
    (h : (a i : F) + (a j : F) = 1) : symbol a = 0 := by
  wlog hlt : i.val < j.val generalizing i j
  · apply this j i (Ne.symm hij) (by simpa [add_comm] using h)
    have hne : i.val ≠ j.val := fun heq => hij (Fin.ext heq)
    omega
  by_cases hadj : i.val + 1 = j.val
  · exact steinberg a i j hadj h
  let k : Fin n := ⟨i.val + 1, by omega⟩
  have hik : i ≠ k := by intro heq; have := congrArg Fin.val heq; dsimp [k] at this; omega
  have hkj : k ≠ j := by intro heq; exact hadj (congrArg Fin.val heq)
  rw [symbol_skew a k j hkj]
  have hz : symbol (Function.update (Function.update a k (a j)) j (a k)) = 0 := by
    apply steinberg _ i k rfl
    simpa [hik, Ne.symm hik, hij, Ne.symm hij, hkj, Ne.symm hkj] using h
  rw [hz, neg_zero]

/-- Insertion in arbitrary distinct coordinates descends through degree-two Milnor K-theory. -/
def pairMap (a : SymbolTuple F n) (i j : Fin n) (hij : i ≠ j) :
    MilnorK.K2.Group F →ₗ[ℤ] K F n :=
  MilnorK.K2.lift (pairInsertBilinear a i j hij) (by
    intro b c h
    apply steinberg_of_ne _ i j hij
    simpa [hij] using h)

/-- The arbitrary pair map substitutes precisely the requested entries. -/
@[simp] theorem pairMap_symbol (a : SymbolTuple F n) (i j : Fin n) (hij : i ≠ j)
    (b c : Fˣ) :
    pairMap a i j hij (MilnorK.K2.symbol b c) =
      symbol (Function.update (Function.update a i b) j c) := rfl

/-- Two distinct coordinates with entries `(b,-b)` give zero. -/
theorem symbol_update_self_neg (a : SymbolTuple F n) (i j : Fin n) (hij : i ≠ j)
    (b : Fˣ) :
    symbol (Function.update (Function.update a i b) j (-b)) = 0 := by
  have h := congrArg (pairMap a i j hij) (MilnorK.K2.symbol_self_neg b)
  simpa only [pairMap_symbol, map_zero] using h

/-- Repeated entries in distinct positions retain the `-1` contribution. -/
theorem symbol_update_self (a : SymbolTuple F n) (i j : Fin n) (hij : i ≠ j)
    (b : Fˣ) :
    symbol (Function.update (Function.update a i b) j b) =
      symbol (Function.update (Function.update a i b) j (-1)) := by
  have h := congrArg (pairMap a i j hij) (MilnorK.K2.symbol_self b)
  simpa only [pairMap_symbol] using h

/-- A repeated coordinate can be replaced by `-1`, in either relative order. -/
theorem symbol_self (a : SymbolTuple F n) (i j : Fin n) (hij : i ≠ j)
    (h : a i = a j) : symbol a = symbol (Function.update a j (-1)) := by
  have hs := symbol_update_self a i j hij (a i)
  simp only [Function.update_eq_self] at hs
  simpa only [h, Function.update_eq_self] using hs

end MilnorK
