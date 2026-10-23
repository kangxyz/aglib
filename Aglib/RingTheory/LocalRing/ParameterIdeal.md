# Actual parameter ideals in local rings

`IsLocalRing.exists_parameter_finset` constructs a finite set of d
elements in a Noetherian local ring of Krull dimension d, whose generated
ideal has radical equal to the actual maximal ideal.
`exists_principal_parameter_of_dimLE_one` gives a single such element
in dimension at most one, including dimension zero.

The proof uses native
`Ideal.exists_finset_card_eq_height_of_isNoetherianRing` at the actual
maximal ideal. Its stated conclusion places that maximal ideal among
the minimal primes of the generated ideal and gives the required
cardinality. Every prime in a local ring lies below the maximal ideal.
Minimality therefore makes the maximal ideal the only prime over the
generated ideal, which identifies the radical. The stronger global
primary-ideal wording in the native theorem's docstring is not used
for an arbitrary nonmaximal prime.

In dimension at most one the finite set has at most one element. If it
is empty, zero is the required parameter. Otherwise the set is an
actual singleton. The chosen element belongs to the maximal ideal
because its generated ideal does.

`IsLocalRing.exists_parameter_pair_containing` takes a Noetherian local
domain of dimension at most two and a specified nonzero element a in
its actual maximal ideal. It constructs x in that maximal ideal with

```text
radical (Ideal.span {a} ⊔ Ideal.span {x}) = maximalIdeal R.
```

The construction uses the literal quotient Q=R/(a) and its original
quotient map q. Nonvanishing of a in the domain makes it a
nonzerodivisor, so the native quotient dimension inequality gives
dim(Q)≤1. Its properness gives the actual local-ring structure on Q.
Choose the principal parameter of Q and lift that actual element to x
in R. The original local quotient map proves x lies in maximalIdeal R.

The image of (a,x) under q is exactly the chosen principal ideal of Q.
Pull its radical equation back along q. Native radical-comap and
quotient map/comap formulas, together with the actual kernel ker(q)=(a),
give the displayed radical equality in R. Q need not be reduced,
normal, or regular.

The current R.F2 consumer uses a=(p:R) in mixed characteristic; p is
nonzero in the original characteristic-zero domain and vanishes in
its actual residue field. The finite-set theorem supplies the two
parameters in equal characteristic. These results provide actual
ideals and elements, not a finite regular-model premise.

Source basis: Aglib HEAD `8b93cc5940dc93f39a2eaf05e6985af28250a578`,
Lean 4.34.1, and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The main native sources are `Ideal/KrullsHeightTheorem.lean`,
`Ideal/MinimalPrime/Basic.lean`, `KrullDimension/NonZeroDivisors.lean`,
and the original local quotient-map APIs.
