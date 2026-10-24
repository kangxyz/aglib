# Generation by the evaluation-at-one kernel

For a field `k` and a finite-dimensional commutative `k`-algebra `B` with
`2 ≤ Module.finrank k B`, the original functionals vanishing at `1` generate
the literal native coinduced `B`-module

`(ModuleCat.coextendScalars (algebraMap k B)).obj M`

for every `M : ModuleCat k`. The coefficient module has no finiteness,
nonzero or rank-one hypothesis. The original `k`-valued theorem and its
public API remain available.

The generation theorems take the dimension inequality directly, without
a redundant `FiniteDimensional k B` argument.

`evaluationAtOneWithCoefficients` is the actual restriction--coinduction
counit, viewed as a `k`-linear map. Its apply theorem identifies it with
the original functional evaluated at `1`; its smul theorem retains the native
action `(b • φ)(x) = φ(x * b)`. No `B`-linearity of evaluation is asserted.
This evaluation map is distinct from ordinary algebra trace.

The proof separates the proper `k`-subspace spanned by `1` with a nonzero
`k`-valued functional `ψ` vanishing at `1`, and chooses `a ∈ B` with
`ψ(a) = 1`. For any coefficient-valued functional `φ`, the original linear
functional `η(x) = ψ(x) • φ(1)` vanishes at `1`. Its genuine native
`B`-multiple `a • η` has evaluation `φ(1)`. Subtracting that multiple
from `φ` puts the difference in the original evaluation kernel. This
proves the span is top without choosing a basis or an orientation of `M`,
constructing a replacement dual action, or using a double-dual argument.

The hypotheses impose no reducedness, separability, locality, Gorenstein
property, trace form or nonzero-trace condition. The source and target
rings are kept in the same universe, as required by the current consumer.

The planned geometric consumer is a possibly nonreduced Cartier hyperplane
section `D` of length at least two on a proper Cohen--Macaulay curve. It
must supply genuine adjunction/Serre-duality comparisons identifying its
dualizing sections with this original coinduced module and its boundary
map with this evaluation counit. In particular, a coefficient line such
as `Ext_R^dim(R)(k,R)` can remain the original module; no chosen
identification with `k` is required for this generation step.
Hyperplane data, the boundary normalization, and the pointwise Nakayama
step remain upstream obligations.
This module proves only the algebraic generation statement; it does not
assert curve generation or RDP.
