# Original signed evaluation on module Hom complexes

[Evaluation.lean](Evaluation.lean) constructs
`CochainComplex.HomComplex.evaluation K J` as an actual A-linear map
`K → Hom_A(Hom_A(K,J),J)`. Here A is a commutative ring and K and J are
the original complexes of A-modules. The Hom objects use the native
module-valued construction in [HomComplex.lean](../HomComplex.lean).
There is no projectivity, finiteness, K-injectivity or biduality premise.

For `x ∈ K^p` and a native cochain phi of degree q, the component is
`(-1)^(p*q) • phi^p(x)`. The equation
`evaluationComponent_delta` proves compatibility with the original Hom
differential. The two terms containing the coefficient differential
cancel, leaving the component of evaluation on the original source
differential. For a coefficient concentrated in degree zero, this sign
reduces to `(-1)^p` times ordinary double-dual evaluation.

`evaluation_naturality` retains each original A-linear source chain map.
`evaluationNatTrans` packages that equation for the actual contravariant
Hom functor and its `rightOp` double. Evaluation is constructed in the
A-module category before any restriction of scalars.

The current consumer is [derived evaluation](Derived.lean), followed by
the [coinduction comparison](Coinduction.lean). Invertibility on complexes
whose restrictions are finite R-perfect remains a separate proof using
the original evaluation map. No surface concentration, nonsplit-model
comparison, geometric trace or GR conclusion is asserted here.

Source basis: Aglib `8b93cc5940dc93f39a2eaf05e6985af28250a578`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1. The sign and
component calculation use the pinned native Hom differential. Native
compilation is coordinated by the principal; coupled proof repair stays
with the author.
