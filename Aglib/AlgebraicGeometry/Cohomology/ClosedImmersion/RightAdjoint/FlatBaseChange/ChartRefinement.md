# Refining the original affine quotient chart

Source: [ChartRefinement.lean](ChartRefinement.lean).

For `C : ClosedImmersionAffineQuotientChart i R a` and a commutative
`R`-algebra `S` whose actual spectrum map is an open immersion,
`C.affineOpenRefinement S` is a quotient chart over
`Spec S → Spec R → Y`.

Its ideal is literally `C.ideal.map (algebraMap R S)`.
Its source map is the native quotient-algebra spectrum map followed by
`C.sourceMap`; the two projection laws expose these original maps.
The chart square is obtained by pasting the original quotient pullback
square with `C.square`. No flatness or derived comparison is added.
