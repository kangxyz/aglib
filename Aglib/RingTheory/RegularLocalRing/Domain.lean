/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RegularLocalRing.DimensionZero
public import Aglib.RingTheory.LocalRing.ParameterAvoidance
public import Aglib.RingTheory.RegularLocalRing.ParameterQuotient
/-!
# Regular local rings are domains

The domain theorem is proved by induction on the dimension, using minimal
parameter quotients, prime avoidance, and Nakayama's lemma. No domain,
regular-sequence, or finite-resolution hypothesis is assumed.

## Extraction basis

Transferred from `Quillen.Algebra.RegularLocal.Domain` at source revision
`83629578a3d70787d41ec631f5234af8758716af`, SHA-256
`8539bed6a2a2c8d416bc7586712cb3c95762e3678bb8be07f8ba78b232c27f74`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
universe u
open IsLocalRing

namespace IsRegularLocalRing

/-- Every regular local ring of a specified finite dimension is a domain.
The induction uses a minimal generator avoiding all minimal primes. -/
theorem isDomain_of_regularLocal_dimension (d : ℕ) (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (hd : ringKrullDim R = (d : ℕ)) : IsDomain R := by
  induction d generalizing R with
  | zero =>
    have hf := isField_of_regularLocal_dimension_zero R (by simpa using hd)
    let := hf.toField
    infer_instance
  | succ d ih =>
    have hne : ringKrullDim R ≠ 0 := by rw [hd]; norm_cast
    obtain ⟨x, hx, hx2, havoid⟩ := exists_parameter_avoiding_minimalPrimes R hne
    obtain ⟨hq, hdim⟩ := regularLocal_quotient_parameter R d hd x hx hx2
    have := hq
    have hdomain := ih (R ⧸ Ideal.span {x}) hdim
    exact isDomain_of_prime_parameter R x hx havoid
      ((Ideal.Quotient.isDomain_iff_prime _).mp hdomain)

/-- A regular local ring is a domain. Its dimension is automatically the
finite natural number of minimal generators of its maximal ideal. -/
theorem isDomain_of_regularLocal (R : Type u) [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  isDomain_of_regularLocal_dimension (maximalIdeal R).spanFinrank R
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm

end IsRegularLocalRing
