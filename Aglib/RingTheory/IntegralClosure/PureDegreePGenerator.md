# Integral generators of the original prime-degree field extension

Source: [PureDegreePGenerator.lean](PureDegreePGenerator.lean).

The inputs are a normal domain R, its original fraction field K, and an
original finite purely inseparable extension L/K of prime degree p in
characteristic p, with the original scalar tower R to K to L.

`exists_scaled_integral_generator_of_pure_degree` takes an actual b outside
original K and clears an original nonzero R denominator m. It returns the
literal equality `(z : L) = m • b` with z in `integralClosure R L`. Scaling
by this nonzero original denominator cannot move b into K. Original normality
then puts z^p in R; the coefficient a has no pth root in original K by
Frobenius injectivity on L. Prime degree makes z generate original L over K.

`pureDegreePFieldPresentation` invokes the shared
`IsAdjoinRootMonic.ofPowerRelation` at precisely that z and a. Its root and
map laws retain z and `Polynomial.aeval z`.
`exists_integral_presentation_of_pure_degree` derives an initial nonbase b
from degree not equal to one and assembles all those data, retaining b, m,
z=m*b, a, the original power equation and the original field presentation.

The whole normalization is NOT asserted monogenic, and its module finiteness
is NOT needed by this supplier. Later integral-trace results retain their own
finite-normalization hypotheses. No completion, regularity, dimension,
coefficient section or differential basis is a premise here.

Direct consumers: [RingTheory/Kaehler/PureDegreePTrace/CompleteRegularEntrance](../Kaehler/PureDegreePTrace/CompleteRegularEntrance.md).
