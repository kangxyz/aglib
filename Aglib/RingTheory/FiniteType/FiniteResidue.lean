/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Ring.Int.Field
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Linarith

/-!
# Finite residue fields of finite-type integer algebras


Source: `R5Lab.Aglib.RingTheory.FiniteType.FiniteResidue`.
Packet SHA-256:
`a9cd327f88e4a180b86ecaad029dbdd71b00aecab5be2d496e24941a5ae2f53d`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

namespace Algebra.FiniteType

universe u

private theorem int_isJacobsonRing : IsJacobsonRing ℤ := by
  apply isJacobsonRing_iff_prime_eq.mpr
  intro P hP
  by_cases hP0 : P = ⊥
  · subst P
    apply le_antisymm _ Ideal.le_jacobson
    intro x hx
    have hu : IsUnit (x * x + 1) := (Ideal.mem_jacobson_bot.mp hx) x
    have hunit := Int.isUnit_iff.mp hu
    simp only [Ideal.mem_bot]
    rcases hunit with h | h <;> nlinarith [sq_nonneg x]
  · let : P.IsMaximal := hP.isMaximal hP0
    exact Ideal.jacobson_eq_self_of_isMaximal

private theorem finite_of_moduleFinite_int (F : Type*) [Field F] [Module.Finite ℤ F] :
    Finite F := by
  let p : Ideal ℤ := Ideal.under ℤ (⊥ : Ideal F)
  have hp : p.IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ) (⊥ : Ideal F)
  have hpne : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp Int.not_isField
  let : Finite (ℤ ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hpne
  let : Module.Finite (ℤ ⧸ p) (F ⧸ (⊥ : Ideal F)) :=
    Module.Finite.of_restrictScalars_finite ℤ (ℤ ⧸ p) (F ⧸ (⊥ : Ideal F))
  let : Finite (F ⧸ (⊥ : Ideal F)) := Module.finite_of_finite (ℤ ⧸ p)
  exact Finite.of_equiv (F ⧸ (⊥ : Ideal F)) (RingEquiv.quotientBot F).toEquiv

/-- A field that is finite type over `ℤ` is finite as a set, with no
characteristic or cardinal-finiteness premise. -/
theorem finite_of_finiteType_int (F : Type*) [Field F] [Algebra ℤ F]
    [Algebra.FiniteType ℤ F] : Finite F := by
  let : IsJacobsonRing ℤ := int_isJacobsonRing
  have : Module.Finite ℤ F := by
    convert! finite_of_finite_type_of_isJacobsonRing ℤ F
    exact Subsingleton.elim _ _
  exact finite_of_moduleFinite_int F

/-- Every actual maximal quotient of a finite-type integer algebra is finite.
Its field structure is `Ideal.Quotient.field m`. -/
theorem finite_quotient_of_finiteType_int (A : Type*) [CommRing A] [Algebra ℤ A]
    [Algebra.FiniteType ℤ A] (m : Ideal A) [m.IsMaximal] : Finite (A ⧸ m) := by
  let := Ideal.Quotient.field m
  exact finite_of_finiteType_int (A ⧸ m)

/-- A nontrivial finite-type integer algebra has an actual maximal ideal
whose quotient is finite as a set. -/
theorem exists_finite_maximal_quotient_int (A : Type*) [CommRing A] [Nontrivial A]
    [Algebra ℤ A] [Algebra.FiniteType ℤ A] :
    ∃ m : Ideal A, m.IsMaximal ∧ Finite (A ⧸ m) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  exact ⟨m, hm, finite_quotient_of_finiteType_int A m⟩

/-- The actual quotient map gives a surjective homomorphism to a finite field
of the same universe as the algebra. -/
theorem exists_finiteField_surjective_hom (A : Type u) [CommRing A] [Nontrivial A]
    [Algebra ℤ A] [Algebra.FiniteType ℤ A] :
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (f : A →+* F), Function.Surjective f := by
  obtain ⟨m, hm, hfin⟩ := exists_finite_maximal_quotient_int A
  let : m.IsMaximal := hm
  exact ⟨A ⧸ m, Ideal.Quotient.field m, hfin, Ideal.Quotient.mk m,
    Ideal.Quotient.mk_surjective⟩

end Algebra.FiniteType
