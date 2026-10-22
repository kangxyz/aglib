# Actual projective coordinates over a field

`ProjectiveSpace.exists_coordinateChart_factorization` takes an actual map
from `Spec K` to the native polynomial projective space and returns an
original standard-chart ring map. Its `Spec` map followed by the native
chart immersion is exactly the original map.

`chartHomCoordinates` evaluates the original homogeneous coordinate ratios.
The chosen chart coordinate is one in the same original field. The relative
variant `exists_coordinateChart_factorization_over` proves that the chart
homomorphism preserves the original map `R → K`.

The coordinate type is unrestricted. The categorical factorization uses
the native common universe for the base ring, field and coordinate index;
the algebraic coordinate evaluation permits an independently sized target
ring. No chosen coordinate family, separability, algebraic closure or
projective-point oracle is supplied as an input. A finite coordinate type
can be used directly with denominator and normalized base ideals when
resolving the corresponding rational projective morphism.
