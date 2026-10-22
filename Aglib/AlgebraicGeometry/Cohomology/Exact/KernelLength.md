# Cohomology kernel length

`KernelLength.lean` proves the section-comparison and length steps used in
the reduced-divisor case of Stacks, Lemma 54.8.2 ([0AXJ](https://stacks.math.columbia.edu/tag/0AXJ)).
The objects are the existing module sheaves, their native additive `Sheaf.H`
and `Sheaf.H'`, the original restriction map, and the native connecting map.

For a short exact coefficient sequence, injectivity of the actual H1 restriction
to an open forces a comparison on quotient sections to be injective when:

* comparison-zero sections restrict to zero on that open;
* the comparison detects zero among sections coming from the middle coefficient.

The resulting actual H1 kernel has length bounded by the comparison cokernel.
No dimension, normality or finite-length assumption is needed for this ENat
inequality. A finite normalization colength will make the bound finite.
`h1Kernel_length_le_fixedComparison` retains one fixed comparison map from
the base ring when the original constants map onto middle sections is
surjective. `h1Torsion_length_le_fixedComparison` specializes this to the
native submodule `Submodule.torsionBy` for the original scalar coefficient map.
`h1Torsion_length_le_of_comparisonKernel` derives the base-section kernel
condition from the fixed comparison map's kernel `(a)`, as occurs for an
injective reduced-divisor map into its normalization. It does not assume
injectivity of the quotient-section comparison.

For the surface application, use the actual sequence
`0 → O_X --a→ O_X → O_Z → 0`, where `Z` is cut out by the original nonzero
element. The comparison is restriction to the strict transform followed by its
map into the normalization of the reduced base divisor. The punctured-base H1
injection is the separate geometric assertion in Stacks 54.7.5
([0AXB](https://stacks.math.columbia.edu/tag/0AXB)). The two displayed kernel
conditions retain its concrete applicability obligations. Normalization
finiteness and finite normalization colength are additional explicit inputs;
no regular resolution or excellence consequence is assumed implicitly.

The current consumer is the fixed-element H1 torsion bound in the separable
finite-cover route to resolution of the original excellent Weierstrass surface.
This module does not yet supply the punctured-base injection, finite
normalization, the full uniform H1 bound, or a resolving blowup sequence.
