# Original negative Cartier coefficient sequence

`idealTensorQuotientSequence_shortExact` proves short exactness of the
existing sequence

`M ⊗ I → M → i_* i^* M`

for a closed immersion with locally rank-one ideal `I`, when its original
positive Cartier section on `M` is monic. It introduces no replacement row
or quotient map: the second arrow is the original adjunction unit.

The proof reuses `cartierIdealAction_mono`, the native braiding and unitors,
`idealTensorQuotientSequence_exact`, and the original quotient-unit
epimorphism. The module `M` is arbitrary; quasicoherence, finite
presentation and invertibility of `M` are not required.

The immediate consumer is coefficient-canonical vanishing on the ordinary
maximal-ideal blowup: the actual canonical Cartier regularity supplies the
monicity, and tensoring this sequence by the original exceptional ideal
powers supplies its cohomological filtration.
