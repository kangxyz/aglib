/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Data.Nat.Prime.Basic

/-! # Positive-annihilator induction with original categorical maps

The coefficient predicate only needs kernels and cokernels of arrows between
known coefficients. The actual scalar kernel inclusion and its cokernel
projection produce each extension; no arbitrary-subobject closure is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

universe u v

/-- A kernel/cokernel-stable coefficient class admits positive-annihilator
induction for every extension-stable target property. Only prime divisors of
the original annihilator are tested. -/
theorem property_of_positive_annihilator
    {C : Type u} [Category.{v} C] [Abelian C]
    (Q P : ObjectProperty C)
    (hkernel : ∀ {F G : C} (a : F ⟶ G), Q F → Q G → Q (kernel a))
    (hcokernel : ∀ {F G : C} (a : F ⟶ G), Q F → Q G → Q (cokernel a))
    (hzero : ∀ F : C, IsZero F → P F)
    (hstep : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    (n : ℕ) (hn : 0 < n)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ n →
      ∀ F : C, Q F → p • 𝟙 F = 0 → P F)
    (F : C) (hF : Q F) (hkill : n • 𝟙 F = 0) : P F := by
  suffices ∀ m : ℕ, 0 < m → m ∣ n → ∀ F : C,
      Q F → m • 𝟙 F = 0 → P F from
    this n hn (dvd_refl n) F hF hkill
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm hmn F hF hk
    by_cases h1 : m = 1
    · apply hzero F
      apply (IsZero.iff_id_eq_zero F).mpr
      simpa only [h1, one_nsmul] using hk
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd h1
    let a : F ⟶ F := (m / p) • 𝟙 F
    let i := kernel.ι a
    let S := ShortComplex.cokernelSequence i
    have hS : S.ShortExact := {
      exact := ShortComplex.cokernelSequence_exact i
      mono_f := by change Mono (kernel.ι a); infer_instance }
    have hK : Q (kernel a) :=
      hkernel a hF hF
    have hQ : Q (cokernel i) :=
      hcokernel i hK hF
    have hmK : (m / p) • 𝟙 (kernel a) = 0 := by
      apply (cancel_mono i).mp
      rw [Preadditive.nsmul_comp, Category.id_comp, zero_comp]
      simpa only [a, Preadditive.comp_nsmul, Category.comp_id] using kernel.condition a
    have hmp : (m / p) * p = m := Nat.div_mul_cancel hpm
    have hpa : (p • 𝟙 F) ≫ a = 0 := by
      simpa only [a, Preadditive.nsmul_comp, Category.id_comp, ← mul_nsmul, hmp] using hk
    let l : F ⟶ kernel a := kernel.lift a (p • 𝟙 F) hpa
    have hl : l ≫ i = p • 𝟙 F := kernel.lift_ι a (p • 𝟙 F) hpa
    have hpQ : p • 𝟙 (cokernel i) = 0 := by
      apply (cancel_epi (cokernel.π i)).mp
      rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero]
      calc
        p • cokernel.π i = (p • 𝟙 F) ≫ cokernel.π i := by
          rw [Preadditive.nsmul_comp, Category.id_comp]
        _ = (l ≫ i) ≫ cokernel.π i := by rw [hl]
        _ = 0 := by rw [Category.assoc, cokernel.condition, comp_zero]
    have hdiv : m / p ∣ n := (show m / p ∣ m from ⟨p, hmp.symm⟩).trans hmn
    exact hstep S hS
      (ih (m / p) (Nat.div_lt_self hm hp.one_lt)
        (Nat.div_pos (Nat.le_of_dvd hm hpm) hp.pos) hdiv (kernel a) hK hmK)
      (hprime p hp (hpm.trans hmn) (cokernel i) hQ hpQ)

end CategoryTheory.ObjectProperty
