# Finite coefficient expansion in two formal variables

Let `k₀ → k` be the supplied algebra map between fields, let `b` be a
`k₀`-basis of `k` indexed by a finite type `D`, and let `q` be a nonzero
natural number. This module constructs a basis of the original ring
`MvPowerSeries (Fin 2) k` over `MvPowerSeries (Fin 2) k₀` for the scalar map

```text
map (algebraMap k₀ k), followed by expand q.
```

The map sends the two base variables to the `q`-th powers of the original
variables. `scalarMap` names this ring homomorphism, and `scalarAlgebra`
installs exactly its scalar action. The result does not use the default
unexpanded coefficient action in its place. No characteristic assumption
is needed.

`basis` is indexed by `D × (Fin 2 → Fin q)`. Its value at `(d, r)` is the
literal monomial with coefficient `b d` and exponent vector `r`; the theorem
`basis_apply_prod` also writes it as

```text
C (b d) * ∏ j : Fin 2, X j ^ (r j : ℕ).
```

For a series `f`, the coefficient at `n` of its `(d, r)` coordinate is

```text
b.repr (coeff (q • n + residue r) f) d.
```

This is `coeff_basis_repr`. The reconstruction is the finite sum of these
coordinate series multiplied by the displayed monomials. Coefficients in
different residue classes vanish in one another's positions. In the same
residue class, the inverse identities reduce to the given coefficient
basis's `repr_sum_self` and `sum_repr` identities. Thus infinitely many
coefficients of `f` are retained as full coordinate series.

`synthesis` is a linear map for a supplied series algebra structure.
`synthesisEquiv` proves that it and the coefficientwise extraction map are
inverse whenever that structure's algebra map equals `scalarMap`.
`basisOfAlgebraMap` exposes this compatibility form for consumers which
already have the same scalar structure installed. The main `basis`,
`module_free`, and `module_finite` declarations install the original
`scalarAlgebra` themselves. The compatibility theorems retain the nonzero
`q` witness and the equality of the scalar maps as explicit parameters;
the coordinate theorem also installs this action in its statement. The
finite/free consequences retain the given coefficient basis and require
only `Finite D`, choosing an enumeration inside their proofs.
Linearity is proved by finite-sum identities;
no continuity assumption or topological generation argument is used.

The immediate consumer is the R.B4 finite presentation of `k[[u,v]]` over
`k_J[[u^p,v^p]]`: take `q = p` and the actual coefficient basis of `k/k_J`.
Construction of the one fixed p-basis complement family, its intersection
properties, the algebraic Kähler basis, and nonzero-differential detection
are subsequent obligations. This leaf does not claim any of those results
or the R.B5/R.B7 differential-trace and cohomology conclusions.

The coefficient regrouping argument corresponds to
[Stacks 07P5](https://stacks.math.columbia.edu/tag/07P5), specialized to two
formal variables; the displayed basis formula gives the stronger finiteness
conclusion used here.
