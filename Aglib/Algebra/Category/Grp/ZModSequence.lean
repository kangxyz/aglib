/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# The actual cyclic-group extension sequence

Multiplication by n embeds Z/m in Z/(mn), with quotient Z/n, when n is positive.
The first arrow is an additive homomorphism, not a ring homomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ZMod

/-- The integer representative map whose quotient is the cyclic inclusion. -/
def integerMultiple (m n : ℕ) : ℤ →+ ZMod (m * n) where
  toFun z := (z : ZMod (m * n)) * (n : ZMod (m * n))
  map_zero' := by simp
  map_add' a b := by simp [add_mul]

/-- Multiplication by n, descended through the integer quotient defining Z/m. -/
def mulInclusion (m n : ℕ) : ZMod m →+ ZMod (m * n) :=
  ZMod.lift m ⟨integerMultiple m n, by
    change ((m : ℤ) : ZMod (m * n)) * (n : ZMod (m * n)) = 0
    rw [Int.cast_natCast, ← Nat.cast_mul, ZMod.natCast_self]⟩

@[simp] theorem mulInclusion_intCast (m n : ℕ) (z : ℤ) :
    mulInclusion m n (z : ZMod m) = (z : ZMod (m * n)) * n :=
  ZMod.lift_coe _ _ _

/-- The original cyclic reduction homomorphism. -/
def mulReduction (m n : ℕ) : ZMod (m * n) →+ ZMod n :=
  (ZMod.castHom (dvd_mul_left n m) (ZMod n)).toAddMonoidHom

@[simp] theorem mulReduction_intCast (m n : ℕ) (z : ℤ) :
    mulReduction m n (z : ZMod (m * n)) = (z : ZMod n) :=
  map_intCast (ZMod.castHom (dvd_mul_left n m) (ZMod n)) z

/-- Positivity gives injectivity by cancellation in the actual integer divisibility relation. -/
theorem mulInclusion_injective (m n : ℕ) (hn : 0 < n) :
    Function.Injective (mulInclusion m n) := by
  apply (ZMod.lift_injective m).mpr
  intro z hz
  change (z : ZMod (m * n)) * (n : ZMod (m * n)) = 0 at hz
  have hz' : ((m * n : ℕ) : ℤ) ∣ z * (n : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by
      simpa only [Int.cast_mul, Int.cast_natCast] using hz)
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
  exact (mul_dvd_mul_iff_right hn').mp (by simpa only [Nat.cast_mul] using hz')

/-- Reduction is surjective, with lifts given by the same integer representatives. -/
theorem mulReduction_surjective (m n : ℕ) : Function.Surjective (mulReduction m n) := by
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  exact ⟨(z : ZMod (m * n)), mulReduction_intCast m n z⟩

/-- Exactness is the literal divisibility of an integer representative by n. -/
theorem mulSequence_functionExact (m n : ℕ) :
    Function.Exact (mulInclusion m n) (mulReduction m n) := by
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  rw [mulReduction_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨(t : ZMod m), ?_⟩
    rw [mulInclusion_intCast, ht]
    simp only [Int.cast_mul, Int.cast_natCast, mul_comm]
  · rintro ⟨y, hy⟩
    obtain ⟨t, rfl⟩ := ZMod.intCast_surjective y
    have h := congrArg (mulReduction m n) hy
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd z n).mp
    simpa [mulReduction, mulInclusion_intCast] using h.symm

/-- The actual short complex of cyclic additive groups. -/
def mulSequence (m n : ℕ) : ShortComplex AddCommGrpCat.{0} :=
  ShortComplex.mk (AddCommGrpCat.ofHom (mulInclusion m n))
    (AddCommGrpCat.ofHom (mulReduction m n)) (by
      ext x
      exact ((mulSequence_functionExact m n) (mulInclusion m n x)).mpr ⟨x, rfl⟩)

/-- The cyclic extension is short exact; no abstract extension oracle is used. -/
theorem mulSequence_shortExact (m n : ℕ) (hn : 0 < n) :
    (mulSequence m n).ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · exact (ShortComplex.ab_exact_iff_function_exact _).mpr (mulSequence_functionExact m n)
  · exact (AddCommGrpCat.mono_iff_injective _).mpr (mulInclusion_injective m n hn)
  · exact (AddCommGrpCat.epi_iff_surjective _).mpr (mulReduction_surjective m n)

end ZMod
