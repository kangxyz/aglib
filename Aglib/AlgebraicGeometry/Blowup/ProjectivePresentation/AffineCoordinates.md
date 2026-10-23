# Original affine coordinates of the tautological quotient

[AffineCoordinates.lean](AffineCoordinates.lean) retains the actual
`BlowupDatum (affineCenter A I)`, its original canonical ideal quotient,
and its saturated affine atlas.

`idealSection A I b` constructs the section associated to the original
element `b : I`. It uses the actual kernel of the quotient map `A → A/I`,
the native affine ideal comparison, and the original closed-image
comparison. Its inclusion is multiplication by `b`.

`tautologicalSection` applies the canonical tautological quotient to the
pulled original section. On the saturated chart with denominator `a`,
`chartSection_eq_ratio` identifies this section with multiplication by
the actual ratio `b/a`, followed by `IdealFrames.chartFrame B a`. The
proof uses the original denominator equation and cancels the original
ideal inclusion only after pullback along the original open chart.

`chartSectionAfterMap_eq_ratio` then pulls this proved equality through
an arbitrary ring homomorphism from that chart ring. It retains the
actual composite scheme morphism and the original pulled frame. There
is no flatness, domain, reducedness, or injectivity assumption on the
additional ring map. No ideal inclusion after this additional base
change is cancelled.

The current consumer is the comparison between the actual finite
tautological coordinate family and the polynomial quotient of the full
scalar-extended Rees algebra. These formulas do not identify a literal
base-changed blowup with the blowup of the image ideal. They do not
assert that the latter image ideal remains Cartier, or prove closedness
of the global coordinate map or projectivity of a blowup chain.
