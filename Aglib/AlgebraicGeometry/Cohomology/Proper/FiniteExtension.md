# Uniform first cohomology under finite separable extension

`NormalModificationH1Bounded A` means that one natural number bounds the
length of the original structure-sheaf H1 on every normal integral proper
birational model over `A`. The module action comes from that model's actual
structural map to `Spec A`. This predicate records boundedness and does not
assert resolution, rationality or projectivity of the supplied model.

`normalModificationH1Bounded_of_finite_separable` transfers this property
along the original finite faithful local algebra `A → B`. Both rings are
normal Noetherian local domains of dimension two, with their actual Nagata
properties. Separability is stated for the literal spectrum function-field
map of the original algebra, rather than for an unrelated field action.
Residue separability, flatness and invertibility of the field degree are
not required.

The proof fixes the field degree `r`, trace-lattice discriminant `d` and
residue degree `e` before any upper model. Original field separability gives
`d ≠ 0`; faithful scalar action gives `image(d) ≠ 0`. The uniform scalar-torsion
theorem then chooses a single `N_d` for that upper-ring scalar. If `N_A` is
the lower bound, the transferred bound is

```text
N_B = N_d * e + r * N_A.
```

For each original upper model, general finite domination constructs normal
models `X,Y`, a finite map `Y → X` and a proper birational map from `Y` to
the supplied model. Both original base squares are retained. The actual H1
map to `Y` is injective. The actual trace-coordinate and adjugate maps bound
H1 of `Y` by its fixed scalar torsion and the original lower H1. Applying
the two previously fixed bounds gives the formula above. The coordinate
map is only base-linear; restriction of the upper action accounts for `e`.

`normalModificationH1Bounded_of_vanishing` gives the bound zero from the
original universal vanishing property. In particular,
`normalModificationH1Bounded_of_regularLocal` uses pre-resolution regular
local rationality. The general transfer theorem also applies when the
lower bound is positive.

The finite-domination supplier works for inseparable extensions as well.
Only the discriminant nonvanishing step here uses separability. The pure
degree-p bound, resolution of rational double points, descent and the final
surface resolution criterion are separate results.

The implementation uses
`Surfaces/Birational/FiniteDomination`, `Cohomology/DirectImage/Finite/Trace`,
`Cohomology/Proper/ScalarTorsion`, and the original proper-birational H1
injection. No theorem assumes its desired dominating model or cohomology
factorization as an input.
