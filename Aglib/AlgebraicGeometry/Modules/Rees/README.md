# Geometric Rees image coefficients

`Image.lean` constructs the actual image of a pullback adjunction unit along
an affine morphism. It proves quasicoherence and, over a locally Noetherian
target, finite type when the source coefficient has finite type. The proof
uses a quotient of the source. It does not claim that the direct-image
codomain is coherent or that the unit is injective.

`Geometry.lean` specializes to base change to the native `reesAlgebra I`,
followed by the iterated base change along its inclusion into `A[t]`.
It retains the original projections and actual quotient onto the image.

`AffineImage.lean` records surjectivity onto actual image sections and
identifies the range of the image inclusion with the range of the original
section map on an affine spectrum, under quasicoherence.

The lower module calculation is
`Aglib.RingTheory.ReesAlgebra.ModuleImage`: the canonical map
`reesAlgebra I ⊗[A] M → PolynomialModule A M` has image precisely the native
submodule of the adic filtration. This statement makes no flatness assumption.

The original-cohomology finiteness application belongs to
`Cohomology/FormalFunctions/ReesFiniteness.lean`. Comparison with the direct
sum of ideal-power cohomology is a separate obligation, not an assumption
or a conclusion of the image construction alone.

`AffineOpenImage.lean` supplies the corresponding actual section-range
normalization on arbitrary affine opens, including the chosen categorical
image. `AffineCoordinates.lean`, `AffineCoordinatesImage.lean`, and
`AffineCoordinatesRestriction.lean` give the tensor description of the original
pullback sections and identify the actual image sections with the native adic
Rees submodule. The comparison retains the actual unit quotient, original
inclusion, restriction maps, and homogeneous monomial action.
