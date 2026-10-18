/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.PolynomialResidue
public import Aglib.KTheory.MilnorK.K3.Symbols
public import Mathlib.Data.DFinsupp.Module

/-!
# Finite support of the actual polynomial Milnor K₃ residues

The residues of an arbitrary class in the actual rational-function `K3` have
finite support among monic irreducible polynomials. For a symbol, the support
is contained in the irreducible divisors of its six actual numerator and
denominator polynomials. Division in all three entries reduces vanishing to
the proved polynomial-unit residue theorem. Symbol generation in the nested
tensor quotient then gives finite support for every class.

The resulting dependent finitely supported linear map has the original
`K2 (AdjoinRoot p)` as its coordinate at `p`. No norm, reciprocity, exactness,
or separability hypothesis is used.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.PolynomialResidue

open Polynomial MilnorK.K2

variable (k : Type*) [Field k]

/-- The finite places, with a unique monic representative for each irreducible. -/
abbrev MonicIrreducible := {p : k[X] // p.Monic ∧ Irreducible p}

instance instIrreducible (p : MonicIrreducible k) : Fact (Irreducible p.val) := ⟨p.property.2⟩

variable {k}

/-- A nonzero polynomial has only finitely many monic irreducible divisors. -/
theorem finite_monicIrreducible_divisors (q : k[X]) (hq : q ≠ 0) :
    Set.Finite {p : MonicIrreducible k | p.val ∣ q} := by
  classical
  have h := Set.Finite.preimage (f := fun p : MonicIrreducible k => p.val)
    Subtype.val_injective.injOn
    (Multiset.finite_toSet (UniqueFactorizationMonoid.normalizedFactors q))
  refine h.subset ?_
  intro p hp
  exact (Polynomial.mem_normalizedFactors_iff hq).mpr ⟨p.property.2, p.property.1, hp⟩

/-- A rational-function unit is literally the quotient of its polynomial units. -/
theorem polynomialUnit_num_div_denom (a : (RatFunc k)ˣ) :
    polynomialUnit (a : RatFunc k).num (RatFunc.num_ne_zero a.ne_zero) /
        polynomialUnit (a : RatFunc k).denom (RatFunc.denom_ne_zero _) = a := by
  apply Units.ext
  simpa only [Units.val_div_eq_div_val, polynomialUnit_coe] using
    RatFunc.num_div_denom (a : RatFunc k)

/-- The six actual numerator and denominator polynomials bounding a symbol's support. -/
def symbolSupportPolynomial (a b c : (RatFunc k)ˣ) : k[X] :=
  (a : RatFunc k).num * (a : RatFunc k).denom *
    (b : RatFunc k).num * (b : RatFunc k).denom *
    (c : RatFunc k).num * (c : RatFunc k).denom

/-- All six factors of the support bound are nonzero. -/
theorem symbolSupportPolynomial_ne_zero (a b c : (RatFunc k)ˣ) :
    symbolSupportPolynomial a b c ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (RatFunc.num_ne_zero a.ne_zero) (RatFunc.denom_ne_zero _))
    (RatFunc.num_ne_zero b.ne_zero)) (RatFunc.denom_ne_zero _))
    (RatFunc.num_ne_zero c.ne_zero)) (RatFunc.denom_ne_zero _)

/-- Expanding actual numerators and denominators proves vanishing outside their divisors. -/
theorem residueAt_symbol_zero_of_not_dvd (p : k[X]) [Fact (Irreducible p)]
    (a b c : (RatFunc k)ˣ) (hp : ¬ p ∣ symbolSupportPolynomial a b c) :
    residueAt p (symbol3 a b c) = 0 := by
  have hprime := (Fact.out : Irreducible p).prime
  simp only [symbolSupportPolynomial, hprime.dvd_mul, not_or] at hp
  rcases hp with ⟨⟨⟨⟨⟨hna, hda⟩, hnb⟩, hdb⟩, hnc⟩, hdc⟩
  rw [← polynomialUnit_num_div_denom a, ← polynomialUnit_num_div_denom b,
    ← polynomialUnit_num_div_denom c]
  simp only [symbol3_div_left, symbol3_div_middle, symbol3_div_right, map_sub]
  simp [residueAt_polynomial_units_zero, hna, hda, hnb, hdb, hnc, hdc]

/-- The actual residue support of a symbol is bounded by its six polynomial factors. -/
theorem residueAt_symbol_support_subset (a b c : (RatFunc k)ˣ) :
    {p : MonicIrreducible k | residueAt p.val (symbol3 a b c) ≠ 0} ⊆
      {p | p.val ∣ symbolSupportPolynomial a b c} := by
  intro p hp
  by_contra h
  exact hp (residueAt_symbol_zero_of_not_dvd p.val a b c h)

/-- Finite support for symbols follows from finite polynomial divisors. -/
theorem finite_residueAt_symbol_support (a b c : (RatFunc k)ˣ) :
    Set.Finite {p : MonicIrreducible k | residueAt p.val (symbol3 a b c) ≠ 0} :=
  (finite_monicIrreducible_divisors _ (symbolSupportPolynomial_ne_zero a b c)).subset
    (residueAt_symbol_support_subset a b c)

/-- Classes whose actual residues have finite support form an integer submodule. -/
private def finiteResidueSubmodule : Submodule ℤ (Group (RatFunc k)) where
  carrier := {x | Set.Finite {p : MonicIrreducible k | residueAt p.val x ≠ 0}}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    refine (hx.union hy).subset ?_
    intro p hp
    by_contra h
    have hx0 : residueAt p.val x = 0 := by simpa using fun hn => h (Or.inl hn)
    have hy0 : residueAt p.val y = 0 := by simpa using fun hn => h (Or.inr hn)
    exact hp (by rw [map_add, hx0, hy0, add_zero])
  smul_mem' := by
    intro n x hx
    refine hx.subset ?_
    intro p hp hx0
    exact hp (by rw [map_smul, hx0, smul_zero])

/-- Every actual K₃ class has finite polynomial-residue support. -/
theorem finite_residueAt_support (x : Group (RatFunc k)) :
    Set.Finite {p : MonicIrreducible k | residueAt p.val x ≠ 0} := by
  have h : (finiteResidueSubmodule (k := k)).mkQ = 0 := by
    apply MilnorK.K3.linearMap_ext
    intro a b c
    change (Submodule.Quotient.mk (symbol3 a b c) :
      Group (RatFunc k) ⧸ finiteResidueSubmodule) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (finite_residueAt_symbol_support a b c)
  exact (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.congr_fun h x)

instance instResidueAddCommGroup :
    (p : MonicIrreducible k) → AddCommGroup (MilnorK.K2.Group (AdjoinRoot p.val)) :=
  fun _ => inferInstance

instance instResidueModule :
    (p : MonicIrreducible k) → Module ℤ (MilnorK.K2.Group (AdjoinRoot p.val)) :=
  fun _ => inferInstance

/-- The actual dependent finite-residue map, constructed using proved finite support. -/
def totalResidue : Group (RatFunc k) →ₗ[ℤ]
    Π₀ p : MonicIrreducible k, MilnorK.K2.Group (AdjoinRoot p.val) where
  toFun x := ⟨fun p => residueAt p.val x,
    Trunc.mk ⟨(finite_residueAt_support x).toFinset.val, fun p => by
      classical
      by_cases hp : residueAt p.val x = 0
      · exact Or.inr hp
      · exact Or.inl ((finite_residueAt_support x).mem_toFinset.mpr hp)⟩⟩
  map_add' x y := by
    apply DFinsupp.ext
    intro p
    exact map_add (residueAt p.val) x y
  map_smul' n x := by
    apply DFinsupp.ext
    intro p
    exact map_smul (residueAt p.val) n x

/-- Each coordinate of the total residue is the previously constructed actual residue. -/
@[simp] theorem totalResidue_apply (x : Group (RatFunc k)) (p : MonicIrreducible k) :
    totalResidue x p = residueAt p.val x := rfl

/-- Vanishing of the total residue means vanishing at every finite polynomial place. -/
theorem totalResidue_eq_zero_iff (x : Group (RatFunc k)) :
    totalResidue x = 0 ↔ ∀ p : MonicIrreducible k, residueAt p.val x = 0 := by
  constructor
  · intro h p
    exact DFunLike.congr_fun h p
  · intro h
    exact DFinsupp.ext h

end MilnorK.K3.PolynomialResidue
