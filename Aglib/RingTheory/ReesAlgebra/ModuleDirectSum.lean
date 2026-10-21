/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Filtration
public import Mathlib.Algebra.DirectSum.Module

/-!
# Native polynomial Rees modules and their degree components

The identification with the direct sum sends each actual component to its
polynomial monomial. Coefficients recover the original direct-sum components.
-/

@[expose] public noncomputable section

universe u v
open PolynomialModule DirectSum

namespace Ideal.Filtration

variable {A : Type u} [CommRing A] {I : Ideal A}
  {M : Type v} [AddCommGroup M] [Module A M] (F : I.Filtration M)

/-- Embed a sum of actual filtration components into the polynomial module. -/
def directSumToPolynomial : (⨁ n : ℕ, F.N n) →ₗ[A] PolynomialModule A M := by
  classical
  exact (PolynomialModule.coeffLinearEquiv A A).symm.toLinearMap.comp
    ((finsuppLequivDFinsupp A).symm.toLinearMap.comp
      (DFinsupp.mapRange.linearMap (fun n => (F.N n).subtype)))

@[simp]
theorem directSumToPolynomial_coeff (d : ⨁ n : ℕ, F.N n) (n : ℕ) :
    (F.directSumToPolynomial d).coeff n = (d n : M) := rfl

/-- A direct sum of filtration components takes values in the native Rees submodule. -/
def directSumToSubmodule : (⨁ n : ℕ, F.N n) →ₗ[A] F.submodule :=
  (F.directSumToPolynomial).codRestrict (F.submodule.restrictScalars A)
    (fun d n => (d n).property)

@[simp]
theorem directSumToSubmodule_coeff (d : ⨁ n : ℕ, F.N n) (n : ℕ) :
    (F.directSumToSubmodule d).val.coeff n = (d n : M) := rfl

/-- Native coefficients of a Rees-submodule element form a finite-support sum. -/
def submoduleCoefficients (p : F.submodule) : ⨁ n : ℕ, F.N n :=
  { toFun := fun n => ⟨p.val.coeff n, p.property n⟩
    support' := Trunc.mk ⟨p.val.coeff.support.val, fun n => by
      classical
      by_cases hn : n ∈ p.val.coeff.support
      · exact Or.inl hn
      · right
        apply Subtype.ext
        exact Finsupp.notMem_support_iff.mp hn⟩ }

/-- The canonical direct-sum identification of the native filtration Rees submodule. -/
def directSumSubmoduleEquiv : (⨁ n : ℕ, F.N n) ≃ₗ[A] F.submodule :=
  LinearEquiv.ofBijective F.directSumToSubmodule ⟨by
    intro d e h
    ext n
    exact congrArg (fun p : F.submodule => p.val.coeff n) h,
    fun p => ⟨F.submoduleCoefficients p, by
      apply Subtype.ext
      apply PolynomialModule.ext
      ext n
      rfl⟩⟩

@[simp]
theorem directSumSubmoduleEquiv_coeff (d : ⨁ n : ℕ, F.N n) (n : ℕ) :
    (F.directSumSubmoduleEquiv d).val.coeff n = (d n : M) := rfl

/-- A homogeneous summand is sent to the original polynomial monomial. -/
theorem directSumSubmoduleEquiv_lof (n : ℕ) (m : F.N n) :
    (F.directSumSubmoduleEquiv (DirectSum.lof A ℕ (fun n => F.N n) n m)).val =
      PolynomialModule.single A n (m : M) := by
  apply PolynomialModule.ext
  ext k
  simp only [directSumSubmoduleEquiv_coeff, DirectSum.lof_eq_of,
    DirectSum.of_apply, PolynomialModule.coeff_single, Finsupp.single_apply]
  split_ifs with h
  · subst k
    rfl
  · rfl

end Ideal.Filtration
