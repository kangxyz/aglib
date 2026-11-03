# Original single-unit coherence

Source: [SingleUnit.lean](SingleUnit.lean).

The composition law states that the native single unit for F composed with G,
followed by the original derived composition comparison, equals the native
single unit for G followed by RG of the native single unit for F. Neither
comparison invertibility nor exactness is assumed.

The isomorphism law retains an original ordinary functor isomorphism and the
native derived isomorphism induced from it. Both proofs use the same existing
`rightDerivedSingleUnit`; the local complex arrows are abbreviations for its
original `singleMapHomologicalComplex` components, not a replacement model.

The intended consumer is actual geometric pushforward single-unit coherence,
then ordinary canonical trace composition.

Direct consumers: [AlgebraicGeometry/Cohomology/ProjectionFormula/StructureUnit](../../../../../AlgebraicGeometry/Cohomology/ProjectionFormula/StructureUnit.md).
