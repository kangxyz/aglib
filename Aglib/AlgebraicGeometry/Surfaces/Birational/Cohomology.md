# Finite-length cohomology of proper birational local surfaces

`Hom.isIso_restrict_localPuncturedSpectrum_of_isProper_birational` derives
invertibility of the actual restriction to the complement of the closed
point. The premises are a Noetherian local domain, an integral source, an
actual proper dominant morphism, invertibility of its original
`functionFieldMap`, `NormalStalks` on the target, and target topological
Krull dimension at most two.

Every point of the punctured local spectrum is nonclosed: a closed point
would define a maximal ideal and hence equal the unique local closed point.
The existing proper birational isomorphism-locus theorem therefore puts the
whole punctured spectrum in the actual target isomorphism locus. Native
restriction comparisons give an isomorphism over this entire open.

`Cohomology.moduleCohomology_isFiniteLength_of_proper_birational_surface`
applies the general proper punctured-spectrum theorem to prove finite length
of every positive `Sheaf.H` of every coherent module sheaf, with its original
structural ring action.
`Cohomology.moduleCohomology_one_isFiniteLength_of_proper_birational_surface`
provides the first-cohomology specialization for the local surface duality
consumer.

No source regularity, excellence, Nagata hypothesis, projectivity, field
structure, or trait hypothesis is used. The result proves finite length;
it does not assert a higher-cohomology dimension bound, identify degree-zero
cohomology with the base ring, supply Leray exactness or puncture injectivity,
or complete the full surface comparison package.
