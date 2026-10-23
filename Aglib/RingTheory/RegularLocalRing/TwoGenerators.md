# Two generators of a nonprincipal maximal ideal

Let `R` be a commutative Noetherian normal local domain. If its actual
maximal ideal has `spanFinrank ≤ 2` and is not principal, then
`ringKrullDim R = 2` and `IsRegularLocalRing R`.

`IsLocalRing.ringKrullDim_eq_two_of_spanFinrank_le_two` gives the dimension
statement, and
`IsRegularLocalRing.of_spanFinrank_le_two_of_not_isPrincipal` gives the
native regular-local-ring property. Neither assumes dimension two or
regularity. There is no excellence, residue-field, coefficient-field,
completion, or trait hypothesis.

The wrapper `IsLocalRing.regularLocal_dimension_two_of_span_pair` takes
original elements `u v : R`, the literal ideal equality

```lean
IsLocalRing.maximalIdeal R = Ideal.span ({u, v} : Set R)
```

and nonprincipality of that same maximal ideal. It returns the conjunction
`ringKrullDim R = 2 ∧ IsRegularLocalRing R`. The pair may initially contain
redundancy; the nonprincipality hypothesis and the conclusion rule out a
single generator.

The lower dimension bound is independent of the two-generator hypothesis.
If the dimension were at most one, `Ring.krullDimLE_iff` would give the
native dimension class. Every nonzero prime would then be maximal.
Noetherianity and normality make `R` a native `IsDedekindDomain`.
Mathlib's `maximalIdeal_isPrincipal_of_isDedekindDomain` contradicts the
original nonprincipality assumption. The discrete dimension order thus
gives `2 ≤ ringKrullDim R`.

For the upper bound, the native Krull height theorem gives
`ringKrullDim R ≤ (IsLocalRing.maximalIdeal R).spanFinrank ≤ 2`.
The two bounds give equality. The native
`IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` then gives regularity.
For an actual generating pair, the finite-set span bound supplies
`spanFinrank ≤ 2` directly from those original elements.

The current consumer is the original target local ring in surface
contraction after its actual isomorphism with the normal global-sections
ring has been established. This result supplies the ring-theoretic step;
it does not construct that isomorphism or prove the geometric contraction.
The source basis is native Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612` and Lean 4.34.1.
