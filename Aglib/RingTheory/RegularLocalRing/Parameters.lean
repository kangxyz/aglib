/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RegularLocalRing.Domain
public import Mathlib.RingTheory.Regular.IsSMulRegular
/-!
# Regular first parameters

Every positive-dimensional regular local ring admits a nonzerodivisor
parameter whose quotient is again regular local and has dimension one lower.
Regularity here is mathlib's embedding-dimension definition, and all domain
and quotient properties are conclusions rather than extra assumptions.

## Extraction basis

Transferred from `Quillen.Algebra.RegularLocal.Parameters` at source revision
`83629578a3d70787d41ec631f5234af8758716af`, SHA-256
`2301e5157a8695fc5aff1299a27e2f6e5fd5fe0fe80fdc797df0b78db69d0f5f`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
universe u
open IsLocalRing

namespace IsRegularLocalRing

/-- A nonzero element of a regular local ring acts injectively on the ring. -/
theorem isSMulRegular_of_regularLocal_ne_zero (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (x : R) (hx : x ≠ 0) : IsSMulRegular R x := by
  have := isDomain_of_regularLocal R
  exact IsSMulRegular.of_right_eq_zero_of_smul fun a ha =>
    (mul_eq_zero.mp ha).resolve_left hx

/-- A genuine first-parameter step derived from regularity: the parameter
lies in the maximal ideal, is a nonzerodivisor, and has regular quotient of
dimension exactly one less. -/
theorem exists_regular_parameter (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (d : ℕ) (hd : ringKrullDim R = (d + 1 : ℕ)) :
    ∃ x : R, x ∈ maximalIdeal R ∧ IsSMulRegular R x ∧
      IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      ringKrullDim (R ⧸ Ideal.span {x}) = (d : ℕ) := by
  have hne : ringKrullDim R ≠ 0 := by rw [hd]; norm_cast
  obtain ⟨x, hx, hx2, _⟩ := exists_parameter_avoiding_minimalPrimes R hne
  have hx0 : x ≠ 0 := fun h => hx2 (h ▸ (maximalIdeal R ^ 2).zero_mem)
  exact ⟨x, hx, isSMulRegular_of_regularLocal_ne_zero R x hx0,
    regularLocal_quotient_parameter R d hd x hx hx2⟩

end IsRegularLocalRing
