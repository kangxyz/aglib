# Degree bounds for the actual completed local factors

Import `Aglib.RingTheory.AdicCompletion.FiniteSemilocalDegree`.
The namespace is `AdicCompletion.FiniteSemilocal`.

Let R be a Noetherian local domain and S a finite domain R-algebra. Supply their
actual fraction fields F and E with the original commuting scalar towers.
For `q : Branch R S`, retain the original local ring `Local R S q`, its completion
Qq=`Completed R S q`, and Rhat=`BaseCompletion R` from
[FiniteSemilocal](FiniteSemilocal.md).

`exists_branch_embedding` gives an injective Rhat-linear map

```text
Qq →ₗ[Rhat] (Fin (Module.finrank F E) → Rhat).
```

The proof first constructs the cleared-denominator embedding of the ENTIRE S
into R to the power `[E:F]` using
[FiniteRankEmbedding](../Localization/FiniteRankEmbedding.md). Exact completion
of finite modules preserves this injection. The canonical free-module tensor
comparison identifies its target with Rhat to the same power. Finally the
single q-component is included through the inverse of the actual full completed
product equivalence. Counting the components is not used as a degree estimate.

If Rhat is a domain, `base_injective` proves injectivity of the original map
Rhat→Qq: a scalar in its kernel would annihilate the nonzero image of 1 under
the branch embedding. When R is regular local, `baseCompletion_domain` obtains
this domain hypothesis from regularity of the actual maximal completion.

For an actual domain Qq, `fractionMap` lifts the original map Rhat→Qq→Frac(Qq)
to Frac(Rhat). Its algebra structure is `fractionAlgebra`, and `fractionTower`
proves the original scalar triangle. `fraction_finite` derives finiteness of
this field extension from the already proved finite completed algebra.
`fraction_finrank_le` proves

```text
[Frac(Qq) : Frac(Rhat)] ≤ [E : F].
```

It uses the original fraction-rank identity and the actual linear embedding.
`fraction_finrank_lt` combines this inequality with a supplied strict bound
`[E:F] < n`, as needed in a field-degree induction.

`originalBaseFractionMap` lifts R→Rhat from F to Frac(Rhat).
`originalFieldMap` lifts S→Local(q)→Qq from E to Frac(Qq).
`original_to_factor_injective` proves injectivity of the original localization
followed by completion before requiring the completed factor to be a domain.
Their algebra-map equations preserve all original ring elements, and
`original_field_square` proves commutativity with the original F→E inclusion
by fraction-ring extensionality on R.

`completedBranch_normalDomain` supplies domainhood and normality together for
this same Qq using [NormalSurface](NormalSurface.md). Its inputs retain an
original complete Noetherian local domain A0 of dimension two, the commuting
A0→R→S→Local(q) maps, injectivity and locality of the original A0→Local(q), a
finite original residue-field extension, normality of S, dimension two of
Local(q), and its genuine Nagata property. Normality of S alone is insufficient
and is not used as a general normal-completion assertion.

The surface consumer must instantiate these hypotheses at its selected actual
normalization stalk. The declarations impose no separability, perfectness, or
finite p-rank condition and do not assert a resolution theorem.
