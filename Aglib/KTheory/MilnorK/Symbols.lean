/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Product
public import Aglib.KTheory.MilnorK.K2.Symbols

/-!
# Adjacent sign identities in every Milnor degree

An adjacent pair of coordinates, with all other entries fixed, gives an
actual map out of the existing degree-two Steinberg quotient. Applying the
already proved degree-two identities through this map gives adjacent skew
symmetry, the vanishing of a pair `(a,-a)`, and the replacement of `(a,a)` by
`(a,-1)` in every degree. In particular these identities are consequences of
the defining relations, rather than extra relations or assumptions.
-/

@[expose] public section

noncomputable section

namespace MilnorK

universe u

variable {F : Type u} [Field F] {n : ℕ}

/-- Two distinct entries of a fixed tuple are bilinear in their substituted units. -/
def pairInsertBilinear (a : SymbolTuple F n) (i j : Fin n) (hij : i ≠ j) :
    Additive Fˣ →ₗ[ℤ] Additive Fˣ →ₗ[ℤ] K F n :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun b => AddMonoidHom.toIntLinearMap {
      toFun := fun c => symbol (Function.update (Function.update a i b.toMul) j c.toMul)
      map_zero' := symbol_update_one _ j
      map_add' := fun b c => symbol_mul _ j b.toMul c.toMul }
    map_zero' := by
      apply LinearMap.ext
      intro c
      apply symbol_eq_zero_of_eq_one _ i
      simp [hij]
    map_add' := by
      intro b c
      apply LinearMap.ext
      intro d
      change symbol (Function.update (Function.update a i (b.toMul * c.toMul)) j d.toMul) =
        symbol (Function.update (Function.update a i b.toMul) j d.toMul) +
        symbol (Function.update (Function.update a i c.toMul) j d.toMul)
      simp only [Function.update_comm hij]
      exact symbol_mul _ i _ _ }

/-- The bilinear insertion map evaluates on units as literal coordinate substitution. -/
@[simp] theorem pairInsertBilinear_apply (a : SymbolTuple F n) (i j : Fin n)
    (hij : i ≠ j) (b c : Fˣ) :
    pairInsertBilinear a i j hij (Additive.ofMul b) (Additive.ofMul c) =
      symbol (Function.update (Function.update a i b) j c) := rfl

/-- Adjacent pair insertion descends through the actual degree-two Steinberg quotient. -/
def adjacentPairMap (a : SymbolTuple F n) (i j : Fin n) (hij : i.val + 1 = j.val) :
    MilnorK.K2.Group F →ₗ[ℤ] K F n :=
  MilnorK.K2.lift (pairInsertBilinear a i j (by intro h; subst j; omega)) (by
    intro b c h
    apply steinberg _ i j hij
    have hne : i ≠ j := by intro h; subst j; omega
    simpa [hne] using h)

/-- Adjacent insertion retains the chosen positions and all other coordinates. -/
@[simp] theorem adjacentPairMap_symbol (a : SymbolTuple F n) (i j : Fin n)
    (hij : i.val + 1 = j.val) (b c : Fˣ) :
    adjacentPairMap a i j hij (MilnorK.K2.symbol b c) =
      symbol (Function.update (Function.update a i b) j c) := rfl

/-- An adjacent pair `(b,-b)` makes a symbol vanish, in every degree. -/
theorem symbol_update_adjacent_self_neg (a : SymbolTuple F n) (i j : Fin n)
    (hij : i.val + 1 = j.val) (b : Fˣ) :
    symbol (Function.update (Function.update a i b) j (-b)) = 0 := by
  have h := congrArg (adjacentPairMap a i j hij) (MilnorK.K2.symbol_self_neg b)
  simpa only [adjacentPairMap_symbol, map_zero] using h

/-- Repeated adjacent entries can be replaced by the pair `(b,-1)`. -/
theorem symbol_update_adjacent_self (a : SymbolTuple F n) (i j : Fin n)
    (hij : i.val + 1 = j.val) (b : Fˣ) :
    symbol (Function.update (Function.update a i b) j b) =
      symbol (Function.update (Function.update a i b) j (-1)) := by
  have h := congrArg (adjacentPairMap a i j hij) (MilnorK.K2.symbol_self b)
  simpa only [adjacentPairMap_symbol] using h

/-- Interchanging two adjacent entries negates the symbol in every degree. -/
theorem symbol_update_adjacent_skew (a : SymbolTuple F n) (i j : Fin n)
    (hij : i.val + 1 = j.val) (b c : Fˣ) :
    symbol (Function.update (Function.update a i b) j c) =
      -symbol (Function.update (Function.update a i c) j b) := by
  have h := congrArg (adjacentPairMap a i j hij) (MilnorK.K2.symbol_skew b c)
  simpa only [adjacentPairMap_symbol, map_neg] using h

/-- Adjacent skew symmetry stated directly for the original tuple. -/
theorem symbol_adjacent_skew (a : SymbolTuple F n) (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    symbol a = -symbol (Function.update (Function.update a i (a j)) j (a i)) := by
  simpa only [Function.update_eq_self] using
    symbol_update_adjacent_skew a i j hij (a i) (a j)

/-- A repeated adjacent entry is a `-1` entry, without changing other coordinates. -/
theorem symbol_adjacent_self (a : SymbolTuple F n) (i j : Fin n)
    (hij : i.val + 1 = j.val) (h : a i = a j) :
    symbol a = symbol (Function.update a j (-1)) := by
  have hs := symbol_update_adjacent_self a i j hij (a i)
  simp only [Function.update_eq_self] at hs
  simpa only [h, Function.update_eq_self] using hs

end MilnorK
