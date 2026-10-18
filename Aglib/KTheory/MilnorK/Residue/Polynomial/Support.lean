/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.Polynomial.Basic
public import Mathlib.Data.DFinsupp.Module
public import Aglib.Algebra.Polynomial.MonicIrreducible

/-!
# Finite support of the actual all-degree polynomial residues

A symbol's residue support is contained in the finite union of the monic
irreducible divisors of its actual numerator and denominator polynomials.
Outside this union, each rational entry is the image of a quotient of actual
local ring units. The all-unit residue theorem proves vanishing directly,
without expanding the symbol into exponentially many numerator/denominator
choices. Symbol generation gives a dependent finitely supported residue map
on all classes, over every field and in every positive degree.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialResidue

open Polynomial Polynomial.LocalResidue

variable (k : Type*) [Field k]

export Polynomial (MonicIrreducible finite_monicIrreducible_divisors)

variable {k}

/-- Rational units are literally quotients of their polynomial numerator and denominator. -/
theorem polynomialUnit_num_div_denom (a : (RatFunc k)ˣ) :
    polynomialUnit (a : RatFunc k).num (RatFunc.num_ne_zero a.ne_zero) /
        polynomialUnit (a : RatFunc k).denom (RatFunc.denom_ne_zero _) = a := by
  apply Units.ext
  simpa only [Units.val_div_eq_div_val, polynomialUnit_coe] using
    RatFunc.num_div_denom (a : RatFunc k)

/-- Away from the numerator and denominator divisors, a rational unit lifts to a local unit. -/
def localRationalUnit (p : k[X]) [Fact (Irreducible p)] (a : (RatFunc k)ˣ)
    (hn : ¬ p ∣ (a : RatFunc k).num) (hd : ¬ p ∣ (a : RatFunc k).denom) : (Ring p)ˣ :=
  localUnit p (a : RatFunc k).num hn / localUnit p (a : RatFunc k).denom hd

/-- The constructed local unit maps to the original rational unit, without symbol expansion. -/
theorem fieldUnits_localRationalUnit (p : k[X]) [Fact (Irreducible p)]
    (a : (RatFunc k)ˣ) (hn : ¬ p ∣ (a : RatFunc k).num)
    (hd : ¬ p ∣ (a : RatFunc k).denom) :
    MilnorK.K2.DVR.fieldUnits (Ring p) (RatFunc k) (localRationalUnit p a hn hd) = a := by
  rw [localRationalUnit, _root_.map_div,
    fieldUnits_localUnit p _ (RatFunc.num_ne_zero a.ne_zero) hn,
    fieldUnits_localUnit p _ (RatFunc.denom_ne_zero _) hd,
    polynomialUnit_num_div_denom]

/-- If every rational entry is a local unit, its actual residue is zero. -/
theorem residueAt_symbol_zero_of_num_denom (p : k[X]) [Fact (Irreducible p)]
    (n : ℕ) (a : SymbolTuple (RatFunc k) (n + 1))
    (hn : ∀ i, ¬ p ∣ (a i : RatFunc k).num)
    (hd : ∀ i, ¬ p ∣ (a i : RatFunc k).denom) : residueAt p n (symbol a) = 0 := by
  have h : a = MilnorK.K2.DVR.fieldUnits (Ring p) (RatFunc k) ∘
      (fun i => localRationalUnit p (a i) (hn i) (hd i)) := by
    funext i
    exact (fieldUnits_localRationalUnit p (a i) (hn i) (hd i)).symm
  rw [h]
  exact residueAt_ring_units p n _

/-- The finite union of numerator and denominator divisors bounding a symbol's support. -/
def symbolSupportSet {n : ℕ} (a : SymbolTuple (RatFunc k) n) : Set (MonicIrreducible k) :=
  {p | ∃ i, p.val ∣ (a i : RatFunc k).num ∨ p.val ∣ (a i : RatFunc k).denom}

/-- The support bound has one pair of finite divisor sets per entry. -/
theorem finite_symbolSupportSet {n : ℕ} (a : SymbolTuple (RatFunc k) n) :
    (symbolSupportSet a).Finite := by
  change Set.Finite {p : MonicIrreducible k |
    ∃ i, p.val ∣ (a i : RatFunc k).num ∨ p.val ∣ (a i : RatFunc k).denom}
  simp only [Set.ofPred_exists, Set.ofPred_or]
  apply Set.finite_iUnion
  intro i
  exact (finite_monicIrreducible_divisors _ (RatFunc.num_ne_zero (a i).ne_zero)).union
    (finite_monicIrreducible_divisors _ (RatFunc.denom_ne_zero _))

/-- Actual nonzero residues can occur only in the stated numerator/denominator union. -/
theorem residueAt_symbol_support_subset (n : ℕ) (a : SymbolTuple (RatFunc k) (n + 1)) :
    {p : MonicIrreducible k | residueAt p.val n (symbol a) ≠ 0} ⊆ symbolSupportSet a := by
  intro p hp
  by_contra h
  apply hp
  apply residueAt_symbol_zero_of_num_denom
  · exact fun i hi => h ⟨i, Or.inl hi⟩
  · exact fun i hi => h ⟨i, Or.inr hi⟩

/-- Every symbol has finite actual residue support, in every degree. -/
theorem finite_residueAt_symbol_support (n : ℕ) (a : SymbolTuple (RatFunc k) (n + 1)) :
    Set.Finite {p : MonicIrreducible k | residueAt p.val n (symbol a) ≠ 0} :=
  (finite_symbolSupportSet a).subset (residueAt_symbol_support_subset n a)

/-- The classes with finite residue support form an integer submodule. -/
private def finiteResidueSubmodule (n : ℕ) : Submodule ℤ (K (RatFunc k) (n + 1)) where
  carrier := {x | Set.Finite {p : MonicIrreducible k | residueAt p.val n x ≠ 0}}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    refine (hx.union hy).subset ?_
    intro p hp
    by_contra h
    have hx0 : residueAt p.val n x = 0 := by simpa using fun hn => h (Or.inl hn)
    have hy0 : residueAt p.val n y = 0 := by simpa using fun hn => h (Or.inr hn)
    exact hp (by rw [map_add, hx0, hy0, add_zero])
  smul_mem' := by
    intro z x hx
    refine hx.subset ?_
    intro p hp hx0
    exact hp (by rw [map_smul, hx0, smul_zero])

/-- Symbol generation proves finite residue support for every actual quotient class. -/
theorem finite_residueAt_support (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    Set.Finite {p : MonicIrreducible k | residueAt p.val n x ≠ 0} := by
  have h : (finiteResidueSubmodule (k := k) n).mkQ = 0 := by
    apply MilnorK.linearMap_ext
    intro a
    change (Submodule.Quotient.mk (symbol a) :
      K (RatFunc k) (n + 1) ⧸ finiteResidueSubmodule n) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (finite_residueAt_symbol_support n a)
  exact (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.congr_fun h x)

instance instResidueAddCommGroup (n : ℕ) :
    (p : MonicIrreducible k) → AddCommGroup (K (AdjoinRoot p.val) n) :=
  fun _ => inferInstance

instance instResidueModule (n : ℕ) :
    (p : MonicIrreducible k) → Module ℤ (K (AdjoinRoot p.val) n) :=
  fun _ => inferInstance

/-- The actual total finite residue with its proved dependent finite support. -/
def totalResidue (n : ℕ) : K (RatFunc k) (n + 1) →ₗ[ℤ]
    Π₀ p : MonicIrreducible k, K (AdjoinRoot p.val) n where
  toFun x := ⟨fun p => residueAt p.val n x,
    Trunc.mk ⟨(finite_residueAt_support n x).toFinset.val, fun p => by
      classical
      by_cases hp : residueAt p.val n x = 0
      · exact Or.inr hp
      · exact Or.inl ((finite_residueAt_support n x).mem_toFinset.mpr hp)⟩⟩
  map_add' x y := by
    apply DFinsupp.ext
    intro p
    exact map_add (residueAt p.val n) x y
  map_smul' z x := by
    apply DFinsupp.ext
    intro p
    exact map_smul (residueAt p.val n) z x

/-- Total residue coordinates retain the actual finite residue maps. -/
@[simp] theorem totalResidue_apply (n : ℕ) (x : K (RatFunc k) (n + 1))
    (p : MonicIrreducible k) : totalResidue n x p = residueAt p.val n x := rfl

/-- Total finite residue vanishes exactly when every polynomial residue vanishes. -/
theorem totalResidue_eq_zero_iff (n : ℕ) (x : K (RatFunc k) (n + 1)) :
    totalResidue n x = 0 ↔ ∀ p : MonicIrreducible k, residueAt p.val n x = 0 := by
  constructor
  · intro h p
    exact DFunLike.congr_fun h p
  · intro h
    exact DFinsupp.ext h

end MilnorK.PolynomialResidue
