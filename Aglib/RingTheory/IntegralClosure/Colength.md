# Colength of a finite normalization in dimension at most one

Fix the actual map from a ring `R` to its total quotient ring `Q`, expressed
by `[Algebra R Q] [IsFractionRing R Q]`. Write `N = integralClosure R Q`.
`quotient_isTorsion R Q` proves that

```
N / LinearMap.range (Algebra.linearMap R N)
```

is torsion over `R`. For each `b` in `N`, localization supplies `r` in `R`
and a non-zero-divisor `s` in `R` with `s*b = r` in the same `Q`. The
quotient class of `b` is therefore killed by `s`. This step has no
Noetherian, finite-generation, reducedness, domain or separability premise.

`quotient_isFiniteLength` and `quotient_length_ne_top` assume that `R` is
Noetherian of Krull dimension at most one and that the actual `N` is a
finite `R`-module. They use `Module.finiteLength_of_isTorsion`. The result
includes reducible reduced divisors; no choice of a fraction field for
just one component replaces the total quotient ring.

For a supplied surjection `A → R`, with its compatible action on `Q`,
`range_restrictScalars_of_surjective` proves equality between the image of
the original map `A → N` and the restricted image of `R → N`.
`quotient_original_length_ne_top` consequently proves

```
Module.length A
  (N / LinearMap.range (Algebra.linearMap A N)) ≠ ⊤.
```

The proof uses the native equality of lengths under a surjective scalar
map. The original map and module action are retained.

For the intended surface consumer, `A` is the original local surface ring,
`R = A/(a)` is the actual reduced divisor ring, and `Q` is its total
quotient ring. The final displayed quotient is the comparison quotient in
`Cohomology/Exact/KernelLength.lean` when its fixed `c` is the original
structural map to `N`. The finite-normalization premise remains explicit.
This module proves the separate finite-colength implication; it does not
prove excellence implies Nagata, finite normalization of arbitrary
excellent divisors, or resolution of the surface.
