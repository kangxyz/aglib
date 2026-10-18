/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalPrime

/-!
# The actual infinity square for a prime normal rational-function norm

Inversion commutes with the actual transported rational-function norm. Applying
the proved finite `X` square after that literal inversion yields the infinity
square in every Milnor degree. No finite-place or norm compatibility law is
assumed as input.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial PolynomialResidue

variable {k : Type*} [Field k] [CharZero k]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

/-- Infinity residue commutes with the actual prime normal rational-function norm. -/
theorem infinityResidue_rationalFunctionNorm_prime
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    InfinityResidue.residue k n (rationalFunctionNorm (n + 1) p x) =
      polynomialNorm n p (InfinityResidue.residue (AdjoinRoot p.val) n x) := by
  change map n (InfinityResidue.rootXEquiv k).toRingHom
    (residueAt (X : k[X]) n
      (map (n + 1) (RatFunc.inversion k).toRingHom
        (rationalFunctionNorm (n + 1) p x))) = _
  rw [rationalFunctionNorm_inversion]
  exact residueAt_X_rationalFunctionNorm_prime p hp n
    (map (n + 1) (RatFunc.inversion (AdjoinRoot p.val)).toRingHom x)

/-- The infinity square as equality of the original integer-linear maps. -/
theorem infinityResidue_comp_rationalFunctionNorm_prime
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (n : ℕ) :
    (InfinityResidue.residue k n).comp (rationalFunctionNorm (n + 1) p) =
      (polynomialNorm n p).comp (InfinityResidue.residue (AdjoinRoot p.val) n) := by
  apply LinearMap.ext
  intro x
  exact infinityResidue_rationalFunctionNorm_prime p hp n x

end MilnorK.PolynomialNorm
