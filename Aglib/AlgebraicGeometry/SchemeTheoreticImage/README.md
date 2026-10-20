# Actual schematic images and polynomial charts

[Integral](Integral.lean) proves `Scheme.schemeImage_isIntegral` for a
quasi-compact map from an integral scheme. It uses the actual kernel quotient
charts and actual dense image; no field, Noetherian or dimension premise is
added.

[PolynomialCharts](PolynomialCharts.lean) uses the canonical
`Scheme.Modules.Coherent.Pushforward.Finite.chartSectionRingMap`. Polynomial
relations for the original map descend to the actual schematic-image chart.
The stated Noetherian domain dimension bound descends to that chart. Its
appLE and germ comparisons retain the original coefficient maps; an actual
open graph produces a nonzero cleared-denominator relation. The file uses
`Polynomial.graphChart_ringKrullDim_le_one` and the existing actual function
field, without assuming properness, a selected projective line, or a curve
record. The native graph/projectivity constructions are its consumers.

Neither leaf is an unrestricted schematic-image base-change theorem.
