/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.KTheory.MilnorK.Norm.FiniteExtension.InfinityBranches

/-! Regression checks for the original-field infinity norm and branch formula. -/

open MilnorK

universe u
variable (k E : Type u) [Field k] [CharZero k] [Field E]
  [Algebra (RatFunc k) E] [FiniteDimensional (RatFunc k) E]

example (n : ℕ) (x : K E n) :
    infinityTwistNorm k E n x =
      map n (RatFunc.inversion k).toRingHom (finiteExtensionNorm (RatFunc k) E n x) :=
  infinityTwistNorm_eq k E n x

example (n : ℕ) (x : K E (n + 1)) :
    InfinityResidue.residue k n (finiteExtensionNorm (RatFunc k) E (n + 1) x) =
      infinityBranchResidueSum k E n x :=
  infinityResidue_finiteExtensionNorm k E n x
