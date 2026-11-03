# Homothety and concentrated coinduced homology

[Homothety](Homothety.lean) defines the original scalar map
`S[0] → Hom_S(J,J)`: its degree-zero cochain acts by `x ↦ s • x`.
For a map from a regular local ring of specified finite dimension, finite
restricted regular module and the stated K-injective coefficient and
coinduced complexes, this same map is a quasi-isomorphism.
The injective-resolution specialization reuses that construction.

[ConcentratedHomothety](ConcentratedHomothety.lean) assumes ambient Ext
concentration and compares the coinduced complex with the single of its
installed D+ homology. The scalar map remains `s ↦ s • id` after the
self-Hom and self-Ext comparisons.

[FiniteProjectiveDimension](FiniteProjectiveDimension.lean) uses a finite
map `R → S` with `R` regular local of specified finite dimension,
Noetherian `S` and Ext concentration in degree `n`. For that same
coinduced homology `K`, `injdim_S S ≤ dS` implies `pdim_S K ≤ dS+n`.
Locality or normality of `S` is unnecessary for this bound.
Carrier, Ext and selected-derived-category sizes retain their stated
independence. Canonical-module consumers supply concentration and
finite-injective-dimension premises.

Present consumers include [Canonical homology and native self-injective dimension](../../../../RingTheory/Gorenstein/README.md).
