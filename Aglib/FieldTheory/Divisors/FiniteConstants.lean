/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.FieldTheory.Divisors.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Finite constant fields in conditional divisor data

Source: `R5Lab.Aglib.FieldTheory.Divisors.FiniteConstants`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

namespace Field

open IntermediateField

section FiniteConstants

variable {C K : Type*} [Field C] [Field K] [Finite C] [Algebra C K]

/-- A nonzero element algebraic over a finite field has a positive power
equal to one, by finiteness of the intermediate field it generates. -/
theorem exists_pos_pow_eq_one_of_isAlgebraic {x : K}
    (hx : IsAlgebraic C x) (hx0 : x ≠ 0) : ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  have : FiniteDimensional C C⟮x⟯ := adjoin.finiteDimensional hx.isIntegral
  have : Finite C⟮x⟯ := Module.finite_of_finite C
  let y : C⟮x⟯ := ⟨x, mem_adjoin_simple_self C x⟩
  have hy : y ≠ 0 := by
    intro h
    exact hx0 (congrArg (fun z : C⟮x⟯ => (z : K)) h)
  let u : C⟮x⟯ˣ := Units.mk0 y hy
  refine ⟨orderOf u, orderOf_pos u, ?_⟩
  have hu := congrArg (fun z : C⟮x⟯ˣ => ((z : C⟮x⟯) : K)) (pow_orderOf_eq_one u)
  exact hu

end FiniteConstants

namespace DivisorData

variable {C K Div : Type*} [Field C] [Field K] [Finite C] [AddCommGroup Div]
  [IsAddTorsionFree Div] (d : DivisorData C K Div)

/-- The divisor kernel and torsion-free cancellation force every element
algebraic over the actual finite constants to lie in their actual image. -/
theorem mem_constants_range_of_isAlgebraic (x : K) :
    letI := d.constants.toAlgebra
    IsAlgebraic C x → x ∈ d.constants.range := by
  let := d.constants.toAlgebra
  intro hx
  by_cases hx0 : x = 0
  · exact ⟨0, by simpa using hx0.symm⟩
  obtain ⟨n, hn, hpow⟩ := exists_pos_pow_eq_one_of_isAlgebraic hx hx0
  let u : Kˣ := Units.mk0 x hx0
  have hupow : u ^ n = 1 := by
    apply Units.ext
    simpa [u] using hpow
  have hz : n • d.divisor (Additive.ofMul u) = 0 := by
    rw [← d.divisor_pow, hupow]
    exact map_zero d.divisor
  have hdiv : d.divisor (Additive.ofMul u) = 0 :=
    (nsmul_eq_zero_iff_right hn.ne').mp hz
  obtain ⟨a, ha⟩ := (d.kernel_eq_constants u).mp hdiv
  exact ⟨(a : C), congrArg (fun z : Kˣ => (z : K)) ha⟩

/-- Relative algebraic closure of the actual finite constants, expressed in
Mathlib's standard integral-closure interface for the induced field algebra. -/
theorem isIntegrallyClosedIn_constants :
    letI := d.constants.toAlgebra
    IsIntegrallyClosedIn C K := by
  let := d.constants.toAlgebra
  apply isIntegrallyClosedIn_iff.mpr
  refine ⟨d.constants.injective, ?_⟩
  intro x hx
  exact d.mem_constants_range_of_isAlgebraic x hx.isAlgebraic

/-- The relative algebraic closure inside the function field is exactly the
bottom intermediate field, namely the actual embedded finite constants. -/
theorem algebraicClosure_eq_bot :
    letI := d.constants.toAlgebra
    algebraicClosure C K = ⊥ := by
  let := d.constants.toAlgebra
  apply bot_unique
  intro x hx
  exact mem_bot.mpr (d.mem_constants_range_of_isAlgebraic x
    (mem_algebraicClosure_iff.mp hx))

end DivisorData

end Field
