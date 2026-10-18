/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.LaurentConstant
public import Aglib.KTheory.MilnorK.Residue.Polynomial.CompleteCoefficient

/-!
# The actual rational prime-normal norm at the finite linear place

The original rational norm restricts to its complete constant presentation.
The proved complete norm-residue theorem and the actual upper localization
square return the original coefficient-field norm. Every map is constructed;
no local compatibility, tower law, or Laurent scalar-extension is assumed.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue
open PowerSeries.ConstantClosure
open scoped RatFunc

variable {k : Type*} [Field k] [CharZero k]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩
local instance (p : MonicIrreducible k) :
    Fact (Irreducible (X : (AdjoinRoot p.val)[X])) := ⟨irreducible_X⟩

/-- The prime-normal rational norm commutes with the original finite `X` residue
in every Milnor degree and on every original rational-function class. -/
theorem residueAt_X_rationalFunctionNorm_prime
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    map n (InfinityResidue.rootXEquiv k).toRingHom
      (residueAt (X : k[X]) n (rationalFunctionNorm (n + 1) p x)) =
      polynomialNorm n p
        (map n (InfinityResidue.rootXEquiv (AdjoinRoot p.val)).toRingHom
          (residueAt (X : (AdjoinRoot p.val)[X]) n x)) := by
  rw [residueAt_X_rationalFunctionNorm_eq_complete n p (constantPolynomial p)
    (CompleteCoefficientResidue.constantPolynomial_eq_rationalCoefficient_map p)]
  rw [residue_polynomialNorm_laurent_constant p hp]
  rw [← CompleteCoefficientResidue.upperFieldMap_eq_rationalCompletionRootMap]
  rw [CompleteCoefficientResidue.upper_residue_square]

end MilnorK.PolynomialNorm
