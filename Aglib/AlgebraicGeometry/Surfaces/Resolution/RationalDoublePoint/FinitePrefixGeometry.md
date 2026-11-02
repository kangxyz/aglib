# Genuine geometry of finite original singular prefixes

API: [singularPrefix_normal_and_dimensions](FinitePrefixGeometry.lean#L65), [finite_singularSet_datum_of_rational_model](FinitePrefixGeometry.lean#L112), [singularPrefix_parent_fiber_finite](FinitePrefixGeometry.lean#L157).

## Inputs and outputs

The base is a Noetherian Nagata rational local domain of dimension two. The
original model is integral, proper and birational over that same base, with
normal original stalks. A selected actual singular root determines the existing
`SingularPrefix`; no completeness, Gorenstein, cone, future geometry, finite-set
or infinite-path hypothesis is added.

`singularPrefix_normal_and_dimensions` proves normality of each actual endpoint
and dimension two at each actual truncation ancestor. It retains only these
proved properties, not a second prefix or stored chain model. The original
`pointBlowupChain_toBase` supplies the finite chain over its literal `toBase`.

`finite_singularSet_datum_of_rational_model` proves finiteness on the whole
actual next blowup, even if the prefix has no singular child. The thin
`singularPrefix_parent_fiber_finite` then applies the existing actual fibre law.

## Original maps and proof order

Native chain properness, integrality, dominance and function-field comparison
apply to `toBase p`; their composite with the original structural map remains
literal. The existing rational-model stalk theorem supplies centre Nagata,
dimension and rationality. The unique original `PointNormality` theorem gives
normality of the whole next source. Original model dimension and the genuine
Nagata-local-dimension-two J-2 theorem give its finite singular set.

No finite prefix is extended to an infinite path to obtain these properties.
In particular, next-source geometry is proved before any child is chosen.

## Boundary

`FiniteHeight` combines these finite parent fibres with the mixed-path
contradiction and native König to obtain an empty level.
`HeightMultiset` uses the whole next-source finite singular set in global
serialization. `FiniteResolution` proves normal stages of its resulting
ordinary chain before the terminal comparison in `NormalizedResolution`.

Present consumers: [FiniteHeight](FiniteHeight.md), [HeightMultiset](HeightMultiset.md).
