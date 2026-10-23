/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.CyclicCoefficientSequence
public import Mathlib.Data.Nat.Prime.Basic

/-! # Original cyclic-coefficient vanishing from the prime divisors

At a fixed cohomological degree, the actual cyclic short exact sequences reduce
vanishing for any positive order to vanishing for its prime divisors. No CRT
model or arithmetic trivialization is substituted for the original coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Original cyclic vanishing follows from vanishing for every prime dividing the order. -/
theorem cyclic_vanishing_of_prime_divisors (q n : ℕ) (hn : 0 < n)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ n →
      Subsingleton (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod p)) X) q)) :
    Subsingleton (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) X) q) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst n
      apply Sheaf.subsingleton_H_of_isZero
      exact (cyclicCoefficientFunctor X).map_isZero
        (AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of (ZMod 1)))
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
      have hm : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
      have hlt : n / p < n := Nat.div_lt_self hn hp.one_lt
      have hmn : n / p ∣ n := Nat.div_dvd_of_dvd hpn
      let S := (ZMod.mulSequence (n / p) p).map (cyclicCoefficientFunctor X)
      let : Subsingleton (Sheaf.H.{w} S.X₁ q) :=
        ih (n / p) hlt hm (fun l hl hld => hprime l hl (hld.trans hmn))
      let : Subsingleton (Sheaf.H.{w} S.X₃ q) := hprime p hp hpn
      have h := Sheaf.H.subsingleton_middle_of_shortExact
        (cyclicCoefficient_shortExact X (n / p) p hp.pos) q
      change Subsingleton
        (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod (n / p * p))) X) q) at h
      exact Eq.mp (congrArg (fun m : ℕ => Subsingleton
        (Sheaf.H.{w} (ConstantFinite.coefficient (ULift.{u} (ZMod m)) X) q))
          (Nat.div_mul_cancel hpn)) h

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
