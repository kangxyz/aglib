# Cech constructions on topological opens

These leaves use the actual opens of a topological space. Their coefficients
are presheaves; neither leaf adds a sheaf condition or a covering hypothesis.
The declaration namespace remains the native `CategoryTheory.Cech`.

[Restriction](Restriction.lean), imported as
`Aglib.Topology.Sheaves.Cech.Restriction`, contains `intersectFunctor`,
`intersectToId` and `restrictPresheaf` for the original intersection restriction.
`intersectToIic` and `iicInclusion` retain the opens-below adjunction.
`restrictedCech_exactAt_succ` proves positive-degree exactness after restriction
to a selected member, with abelian coefficients and the stated product
universes. `cechCosimplicialIntersectIso` identifies the actual cosimplicial
objects when every family member lies in the fixed open; it retains arbitrary
coefficient categories with the required products.

[Cocycles](Cocycles.lean), imported as
`Aglib.Topology.Sheaves.Cech.Cocycles`, uses a module-valued presheaf on actual
opens. `tupleOpen`, `sectionRes` and `cochainVector` retain the literal finite
intersections, restrictions and product-coordinate maps. The differential
formula and `cechOne_vector_closed` use the original Cech complex.
`cechOne_coboundary_of_exact` and `exists_cechOne_coboundary_of_exact` turn the
stated degree-one exactness and cocycle equations into actual sectionwise
coboundaries. The original space/ring/index universe context is unchanged;
these results do not supply that degree-one exactness premise.

The lower [generic Cech family](../../../CategoryTheory/Sites/SheafCohomology/Cech/README.md)
owns arbitrary-category split exactness, coefficient comparison and generic
module short-exact-sequence calculations. Scheme Cech restriction, injective
coefficient calculations, affine comparison and the actual affine-cohomology
test consume these topological specializations.

This is a source split of the existing implementations at revision
`451aeda6b8bb5b44402b574dd6cf60f912360f8c`, preserving the actual declarations,
conditions, maps and proofs. It introduces no new mathematical assertion.
