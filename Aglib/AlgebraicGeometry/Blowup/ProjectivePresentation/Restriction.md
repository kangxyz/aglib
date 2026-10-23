# Restriction of the original blowup presentation

`restrictedDatum B V` is the literal pullback of the original blowup along
the affine-open map of V, with centre identified as the ideal of the original
sections. `affinePullbackIso` and `chartMap_isPullback` identify its further
arbitrary affine base change with the original fibre-product chart. Their
projection equations keep both the original blowup and source maps.

`degreeOneRestrictionIso` compares the full pulled ideal modules. Its only
inverted ideal comparison is along the original open immersion. The map from
the source affine ring is arbitrary; its image ideal is not substituted for
the full tensor ideal. `localPresentation` pulls the specified original
coproduct epimorphism through this comparison. `localPresentation_framed_row`
retains each original summand in the supplied source frame, and
`localPresentation_generators_span` proves that its recovered generators span
the full tensor module, including possible torsion.

`tautologicalRestrictionIso` uses the open projection induced by the same V.
`tautologicalRestrictionQuotient` proves compatibility with the original
canonical quotient before arbitrary scalar change. `pulledLineRestrictionIso`
and `sourceFrame` are the actual line and source-frame comparisons on the
local fibre product. `pulledQuotient_restriction` transports the canonical
quotient through this square, and `originalRow_restriction` proves the exact
original indexed section equation used by the local projective-map comparison.
The transport proof uses the native adjunction mate correspondence to establish
coherence of the pullback cube; it adds no geometric hypothesis. The regular
`QuotientRestrictionEq` and `RowRestrictionEq` definitions retain these literal
equations at both the abstract proof and concrete specialization, with all
original quotient maps supplied explicitly. Native compiler evidence is
recorded separately against the frozen source bytes.
