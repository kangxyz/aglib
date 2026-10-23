# Degree-one dehomogenization

[DegreeOne.lean](DegreeOne.lean) constructs, in the native
`HomogeneousLocalization.Away` namespace, the ring equivalence

    Away(G,f) ≃ A / (f−1)

for an actual commutative ring `A`, an actual grading `G` by natural
numbers with its `GradedRing` direct-sum structure, and `hf : f ∈ G 1`.
There is no domain, reducedness, nonzero, finite-generation or flatness
hypothesis. Zero and nilpotent denominators are included.

`dehomogenize` uses the original homogeneous decomposition and sends
`a ∈ G n` to the native fraction `a/f^n`. It sends `f` to one, and
`fromQuotient` is its actual quotient descent. `toQuotient` restricts the
ordinary localization lift of the quotient map. The two inverse equations
give `degreeOneQuotientEquiv`.

The numerator formulas state both directions on the original homogeneous
elements and fractions. The degree-zero formulas retain the original
`fromZeroRingHom` and the original quotient map; they supply the coefficient
comparison needed by the scalar-extension consumer.

The current consumer is the comparison between the homogeneous localization
of the full scalar-extended Rees algebra and the tensor product of the
original chart ring. Ordinary tensor-product/quotient base change can use
this equivalence and the relation `1 ⊗ f − 1`. That tensor comparison,
the scheme pullback square and the tautological-section matching are
separate obligations. This leaf proves no surface-projectivity result.
