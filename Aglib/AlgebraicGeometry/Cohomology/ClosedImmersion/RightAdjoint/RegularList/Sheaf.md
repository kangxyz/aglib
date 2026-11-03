# Sheaf realization of the closed right adjoint

## Original resolution naturality

The generic `ResolutionNaturality` interface keeps the actual closed affine
map, quasicoherent source and target coefficients, and their supplied
injective resolutions. It has no regular-list hypothesis.
`closedΓResolutionComplex`, `closedΓResolutionExtAddEquiv` and
`closedΓResolutionMap` retain the original native section complex, ambient
Ext comparison and coefficient-resolution map.
`closedΓResolutionExtAddEquiv_naturality` identifies the induced homology
map with native Ext postcomposition by the original coefficient map.
These existing constructions and proof are public for actual coefficient
transport and overlap comparisons, rather than duplicated downstream.
