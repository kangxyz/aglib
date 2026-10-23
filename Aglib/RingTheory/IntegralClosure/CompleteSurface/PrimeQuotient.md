# Finite normalization of every prime quotient

Let R be a complete Noetherian normal local domain of Krull dimension at
most two. For any prime ideal p, let K be the supplied fraction field of
the actual quotient `C = R/p`, and let L/K be any finite field extension.
The original maps `C → K → L` are retained, with their scalar-tower
compatibility. The theorem

```text
integralClosure.finite_primeQuotient_of_complete_local_normal_dimLE_two
```

proves

```text
Module.Finite C (integralClosure C L).
```

There is no normality assumption on C and no separability assumption on
L/K. The conclusion concerns the literal integral closure for the given
coefficient map, rather than a chosen finite algebra representing it.

The quotient is a domain because p is prime. The canonical surjection
`R → C` gives Noetherianity and localness. Finite-module completeness makes
C complete for the image of the maximal ideal of R; the native image
formula identifies this ideal with the actual maximal ideal of C.

When p is zero, `(RingEquiv.quotientBot R).symm` transfers normality to the
literal quotient. Quotient dimension is at most two. The proof applies
[`finite_of_complete_local_normal_dimLE_two`](../CompleteSurface.lean)
directly to C, K, and L. Only the normality property is transported; the
fraction field, extension, and normalization carrier remain unchanged.

When p is nonzero, choose a nonzero x in p. Since R is a domain, x is a
nonzerodivisor killed by the quotient map. Mathlib's
`ringKrullDim_succ_le_of_surjective` gives

```text
dim(C) + 1 ≤ dim(R) ≤ 2,
```

so C has dimension at most one. The proof then applies
[`finite_of_complete_local_dimLE_one`](../CompleteCurve.lean) to the actual
C, K, and L. This branch permits a nonnormal quotient and an inseparable
extension.

This is the prime-quotient finiteness bridge for the R.F1b consumer. It does
not prove finite-type or localization stability of the Nagata property,
finite normalization of graph algebras, or a resolution theorem. Its
load-bearing suppliers are the complete-surface and complete-curve
normalization theorems, with their stated hypotheses.

Source basis: Aglib HEAD `8b93cc5940dc93f39a2eaf05e6985af28250a578`,
Lean 4.34.1, and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
