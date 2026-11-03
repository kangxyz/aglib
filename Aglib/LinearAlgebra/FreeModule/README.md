# Free modules and rank-one cancellation

`ZModTorsion` proves that vectors annihilated by `d` are `e`-multiples over
`ZMod (d * e)`, with `0 < d`. The source basis theorem retains its actual
`Fin 2` basis and original scalar action. The scalar arithmetic does not assume
`e` positive. These facts support finite-level character coordinates.

[StableRankOne](StableRankOne.md) constructs a cyclic generator of `M` from
an actual basis of `M × Rⁿ` with `n + 1` elements, over any commutative ring.
Its nonzero-ideal consequence proves principality of an actual stably free
ideal in a domain. The cofactor construction uses native alternating maps
and basis determinants; no scheme or Noetherian hypothesis is involved.

[TorsionQuotient](TorsionQuotient.lean) factors two actual surjective
linear maps from the same module over a commutative domain.
The first target has a supplied linear frame, its kernel lies in the
native torsion submodule, and the second target is torsion-free and
nontrivial. The resulting equivalence retains the exact factorization
equation. All carrier universes are independent; no local or Noetherian
hypothesis is added. Canonical ideal-image comparisons use this criterion.
