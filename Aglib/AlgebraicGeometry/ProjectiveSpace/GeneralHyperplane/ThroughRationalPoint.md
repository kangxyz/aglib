# Hyperplanes through a rational point

Source: [ThroughRationalPoint.lean](ThroughRationalPoint.lean).

`ThroughRationalPoint.lean` proves the constrained linear avoidance step using the
native chart rings of polynomial projective space. Its linear forms are actual
finitely supported coefficient vectors, interpreted on chart `i` as
`∑ cⱼ (Xⱼ/Xᵢ)`. Incidence is the original equation `∑ cⱼ aⱼ = 0`.

* `coordinateRingEvaluate` is evaluation of the polynomial chart coordinates at
  `aⱼ/aᵢ`; it is the rational-point chart map when `aᵢ ≠ 0`.
* `exists_coordinateRatio_sub_notMem` proves separation from a different prime
  using polynomial coordinate generation and maximality of the rational-point
  kernel. It does not assume reducedness or an algebraically closed field.
* `exists_linearForm_through_notMem` proves chartwise separation for the genuine
  incidence linear system. If `aᵢ = 0`, the allowed form `Xᵢ` has coefficient one.
  Otherwise the coordinate differences generate the rational-point ideal.
* `exists_linearForm_through_isSMulRegular` applies finite associated-prime
  avoidance to the kernel of actual linear evaluation. It assumes an infinite
  field, finitely many projective coordinates and finitely many finite chart
  modules. The point's chart ideal must not be associated where `aᵢ ≠ 0`.

No global reducedness, perfectness or closure assumption is used. The theorem
also allows the zero vector (then incidence imposes no constraint); to interpret
`a` as a projective rational point the caller supplies a nonzero coordinate.
The exact global-section/chart and point-map adapters are given below, separately
from the chart-module theorem. Final arbitrary-field curve generation still needs
its separate field-extension and descent proof.

Source proof: polynomial-chart generation, maximality of a surjective map to the
base field, and the existing associated-prime finite-union avoidance theorem.

## Original sheaf and point maps

The source also supplies the exact original geometric adapters:

* `linearFormPolynomial` is the genuine homogeneous polynomial `∑ cⱼ Xⱼ`;
  `linearFormSection` is its existing `homogeneousSection` of `O(1)`.
* `homogeneousChartFraction_linearForm` and
  `frameCoefficient_linearFormSection` compare the actual fraction and original
  frame coefficient with the same linear combination of chart ratios.
* `coordinateSectionEvaluate` uses the inverse of native `basicOpenIsoAway`.
  `coordinateSectionEvaluate_frameCoefficient` proves that the original section
  vanishes in this frame whenever `∑ cⱼ aⱼ = 0`.
* `coordinateRingEvaluate_point` identifies its chart map with the same original
  rational-point morphism from `BinaryFormProduct.Field.point`. Rescaling the
  nonzero vector changes no scheme morphism.
* `exists_linearFormSection_through_isSMulRegular` applies avoidance to actual
  chart section modules of finitely many affine-locally finite-type sheaves and
  restricts regularity to every subopen. The exact rational-point kernel must be
  absent from each relevant chart's associated primes.
* `exists_linearFormSection_through_mono` concludes monicity of the native
  `twistingTensorMultiply`, with the original zero-twist isomorphism.

## Local exclusion bridge

`IsSMulRegular.not_mem_associatedPrimes_of_isLocalizedModule_atPrime` rules out
an associated prime `P` when an element of the maximal ideal is regular on the
actual localized module. It uses the original localization `R → S` and original
localized-module map `M → N`. `P` need only be prime; no Noetherian, finite-module,
or maximality hypothesis on `P` is needed. This is the direction needed when a
curve's closed-stalk Cohen–Macaulay parameter is lifted through the original
closed-immersion stalk surjection. Localization transfers association to the
maximal ideal; the weak-associated annihilator witness is contradicted by a
power of the regular element.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/CohenMacaulayCurve/Generation/Hyperplane](../../Cohomology/Duality/Projective/Relative/CohenMacaulayCurve/Generation/Hyperplane.md).
