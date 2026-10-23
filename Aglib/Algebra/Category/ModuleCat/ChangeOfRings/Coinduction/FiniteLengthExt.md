# Scalar annihilators detected by coinduced Ext-two

[FiniteLengthExt.lean](FiniteLengthExt.lean) supplies
`ModuleCat.coinducedExtTwo_scalar_annihilates_iff`. The source R is a
commutative regular local ring with `ringKrullDim R = 2`; native regular
locality includes Noetherianity. A is a commutative ring, and
`sigma : R →+* A` is the actual structural map. Its restricted regular
module A is projective over R. M is the original A-module, and its actual
restriction along sigma has finite length over R.

For each `a : A`, the theorem proves

`(forall x : Ext_A^2(M, Hom_R(A,R)), a • x = 0)`

if and only if `forall m : M, a • m = 0`. Here `Hom_R(A,R)` means the
existing `ModuleCat.coextendScalars sigma` applied to the original ring
module R, with its native action `(a • lambda)(b) = lambda(b*a)`.
The Ext group has its intrinsic A-module action.
`ModuleCat.coinducedExtTwo_annihilator` expresses the same result as equality
of the two actual annihilator ideals in A.

The proof uses the original Ext comparison from
[Projective.lean](Projective.lean). Precomposition by the restriction of
the actual A-linear endomorphism `a • identity_M` corresponds exactly to
scalar multiplication by a on the coinduced A-Ext group. The
[finite-length Ext-two supplier](../../../../../RingTheory/RegularLocalRing/FiniteLengthExtDuality.lean)
then detects whether this restricted endomorphism is zero. Scalar
restriction retains the original underlying function, so this is exactly
annihilation of M by a. The converse uses the same maps in the reverse
direction.

No finiteness, injectivity or locality hypothesis on sigma is added to this
algebra leaf, beyond projectivity of the actual restricted regular module.
There is no Noetherian or normality assumption on A. The supplied finite
length is over R, and is not silently inferred from finite A-length. A
surface consumer must supply the actual restriction-of-scalars length
comparison under its finite local map. The source ring, target ring and
module carriers here share the universe of the existing finite-length
Ext-two supplier; no stronger universe claim is made.

The current B7 consumer uses this equivalence after identifying the
original geometric trace cokernel with this actual A-Ext-two module. The
present theorem does not construct that trace comparison, supply one
uniform annihilator, prove Grauert--Riemenschneider vanishing, or bound
cohomology. It needs neither an injective-hull identification nor a derived
biduality premise. The genuine A-valued derived-dual construction remains
a separate prerequisite for the nonsplit GR argument.

Source basis: Aglib `8b93cc5940dc93f39a2eaf05e6985af28250a578`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1. Native compilation
is coordinated by the principal; the author retains the coupled proof
repair obligation. The passed projective-coinduction and finite-length
Ext-two suppliers remain unchanged.
