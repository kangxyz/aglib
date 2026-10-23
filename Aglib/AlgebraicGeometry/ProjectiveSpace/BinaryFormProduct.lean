/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.BaseChange
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Finite
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Surjective

/-!
# Finite surjective multiplication of original binary forms

For every commutative base ring `R` and every `n`, the original coefficients
of `∏ i, (x i * T + y i * U)` define a finite surjective morphism from the
existing native over-product of `n` unchanged native projective lines to the
existing projective space with `n+1` original coefficient positions.

Coordinate `k` is the coefficient of `T^(n-k) U^k`; the first coordinate is
`∏ i, x i`, and the last is `∏ i, y i`. The empty product maps isomorphically
to projective zero-space. No characteristic, factorial, reducedness or
Noetherian hypothesis occurs.

The morphism commutes with every commutative coefficient-ring map. Its
canonical comparison is the native pullback isomorphism, with the original
source base-change map and multiplication as its two projections.
-/
