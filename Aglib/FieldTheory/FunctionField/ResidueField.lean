/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.FunctionField.DimensionOne
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Actual residue fields of finite-type rings of dimension at most one

The original ring may be nonreduced or reducible. Only the actual prime quotient
is used as a domain; its original residue field is its native fraction field.
-/

@[expose] public noncomputable section

namespace Ideal

variable (k A : Type*) [Field k] [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A] (P : Ideal A) [P.IsPrime]

/-- Each original residue field is algebraic over the constants or over an
actual compatible rational function field in one variable. -/
theorem residueField_algebraic_or_ratFunc_of_dim_le_one
    (hdim : ringKrullDim A ≤ 1) :
    Algebra.IsAlgebraic k P.ResidueField ∨ ∃ a : Algebra (RatFunc k) P.ResidueField,
      letI := a
      Algebra.IsAlgebraic (RatFunc k) P.ResidueField ∧
        IsScalarTower k (RatFunc k) P.ResidueField :=
  Field.algebraic_or_exists_ratFuncAlgebra_of_dim_le_one k (A ⧸ P) P.ResidueField
    ((ringKrullDim_quotient_le P).trans hdim)

end Ideal
