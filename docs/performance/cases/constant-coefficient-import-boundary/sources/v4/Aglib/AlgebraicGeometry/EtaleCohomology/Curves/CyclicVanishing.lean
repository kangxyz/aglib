/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.CyclicCoefficientSequence

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
  exact Sheaf.cyclic_vanishing_of_prime_divisors (cyclicCoefficientFunctor X) q n hn hprime

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
