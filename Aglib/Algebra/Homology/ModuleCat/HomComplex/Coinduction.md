# The original coinduction comparison on Hom complexes

[Coinduction.lean](Coinduction.lean) constructs
`CochainComplex.HomComplex.coinductionComplexIso sigma K I` for an actual
map of commutative rings `sigma : R →+* A`, an original A-complex K and
an original R-complex I. It identifies the restriction to R of
`Hom_A(K, coextendScalars(sigma)(I))` with `Hom_R(Res K,I)`.
No projectivity, exactness, finiteness or injectivity assumption is needed
for this chain-level comparison. The common module carrier universe is
the one required by the native restriction/coinduction adjunction; the
two ring universes remain independent.

The forward map on each original homogeneous cochain evaluates its
coinduced functional at `1_A`. Its inverse sends psi to
`x ↦ (a ↦ psi(a • x))`. The original R-linearity and differential
equations are proved on those same cochains. The comparison is also
identified with native cochain restriction followed by the original
chain counit. `coinductionAdjunction_counit_f` identifies every component
of that mapped adjunction counit with the original R-module counit.
Its differential and source-naturality equations follow
from that same cochain composition and the native differential rules.
Source naturality retains the actual precomposition chain maps.

`coinductionCochainEquiv_apply` and
`coinductionCochainEquiv_symm_apply` retain these exact component equations
for explicit rewriting. They are not global simp rules: native simplification
of the mapped-complex carrier types changes their left-hand sides.

`coinductionCochainEquiv_smul_apply` identifies the native A-action with
source multiplication after the R-linear comparison. No A-action is
assigned to I. The A-module complex already exists before this comparison.

`coinductionDoubleComplexIso` uses the same first comparison, with its
inverse in the contravariant source position. Its evaluation equation
identifies the restriction of the actual signed A-evaluation with the
original signed R-evaluation. Thus a later proof of invertibility over R
can apply to a morphism already constructed in the A-derived category.
It must use reflection of isomorphisms, not presumed faithfulness of
derived scalar restriction.

The current consumer is the finite-R-perfect evaluation proof following
[Derived.lean](Derived.lean). That invertibility proof, the actual
nonsplit C-model comparison, surface concentration and geometric trace
compatibility remain separate. No GR or B7 boundedness conclusion is
asserted here.

Source basis: Aglib `8b93cc5940dc93f39a2eaf05e6985af28250a578`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1. Native compilation
is coordinated by the principal; coupled proof repair stays with the author.
