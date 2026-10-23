# Purely inseparable normalization of a DVR

Fix the original tower `A → K → E`, where A is a domain, K its fraction
field, and E a field. The carrier throughout is the literal
`S = integralClosure A E`, with its original coefficient map and inclusion
in E. The rings and fields may lie in different universes.

`integralClosure.mem_iff_pow_mem_range` applies over an integrally closed A.
For a positive integer n and an actual element u of E whose n-th power lies
in the image of K, it proves

```text
u ∈ integralClosure A E ↔ u^n ∈ (algebraMap A E).range.
```

The forward implication descends integrality to K and uses normality of A.
The reverse implication uses the monic power equation. No Noetherianity,
finiteness, or characteristic assumption is needed for this pointwise lemma.

For a DVR A and a finite field extension E/K,
`isNoetherianRing_of_isDiscreteValuationRing` derives Noetherianity of S as
a ring from the existing one-dimensional finite-rank Krull–Akizuki result.
Separability is not assumed. This theorem does not assert that S is finite
as an A-module.

If E/K is finite and purely inseparable,
`valuationRing_of_isPurelyInseparable` uses Mathlib's actual
`IsPurelyInseparable.HasExponent` witness. It selects
`q = ringExpChar K ^ e > 0`. The base valuation ring contains either the
q-th power of u or its inverse; the monic power equation therefore puts
u or its inverse in S. This proves the valuation-ring property under
the original embedding `S → E`. The characteristic-zero, hence trivial,
purely inseparable case is included by exponential characteristic one.

`isDiscreteValuationRing_of_isPurelyInseparable` combines this valuation
property with the proved Noetherianity. The target is not a field: an
injective integral extension which is a field would force the original
DVR to be a field. Thus the result uses Mathlib's DVR convention, which
excludes fields. No completeness, excellence, coefficient field, Japanese
condition, or finiteness of S over A is assumed.

`algebraMap_isLocalHom` derives localness of the original coefficient map
from integrality and injectivity. `purelyInseparableResidueAlgebra` delegates
to Mathlib's native residue algebra for that local homomorphism. Its
coefficient equation is `purelyInseparableResidueAlgebra_residue`:

```text
residue_A(a) ↦ residue_S(algebraMap A S a).
```

`finite_residueField_of_isPurelyInseparable` proves that this actual residue
extension is finite. It chooses a uniformizer π of A, applies the finite-rank
scalar-quotient theorem to `S / π S`, and factors the actual residue map
through that quotient. Its finite A-length yields finite generation over
the residue field of A. The normalized ring S itself is never supplied as
a finite A-module.

The residue interfaces expose the derived DVR and residue algebra values
as `let` bindings in their result types, rather than requiring callers to
assume a DVR structure on S. Each of those values delegates to the proved
supplier or the native canonical residue construction.

This leaf is the local normalization and finite-residue input for the
two-dimensional residue-layer argument. It does not prove finite
normalization over a two-dimensional base, module finiteness over an
arbitrary DVR, a ramification-degree formula, or a surface-resolution
theorem.

New source basis: Aglib HEAD
`c6f64b5b133624fae3ad8650f456194180be7ba2`, Lean 4.34.1, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Supporting mathematical route:
Stacks Project Lemmas 10.119.10 and 10.119.12,
[031F](https://stacks.math.columbia.edu/tag/031F) and
[00PG](https://stacks.math.columbia.edu/tag/00PG), together with the actual
power criterion. The one-dimensional suppliers and the two-dimensional
scratch argument retain their separate source and review identities.
