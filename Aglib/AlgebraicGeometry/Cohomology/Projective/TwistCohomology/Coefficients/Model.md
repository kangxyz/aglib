# Original bounded twist models with arbitrary coefficients

`Model.lean` owns the original finite Cech complex of `O(d)`, its free and
finite degree-zero homology, sharp acyclicity, and the original bottom-homology
inclusion. Tensoring that inclusion with an arbitrary base module uses the
bounded flat acyclic cone, not a generic homology-preservation assumption.

The coefficient Cech comparison and finite-derived comparison identify the
installed derived global sections of `O(d) ⊗ π*tilde(J)` with the original
single-degree tensor model when `-(n : ℤ) ≤ d`. The original positive sheaf
cohomology vanishes in that range; the native H0 and original large sheaf
cohomology normalizations retain the supplied-resolution compatibility law.

The base ring is any commutative ring. The coefficient module is arbitrary;
no flatness, Noetherianity or relative-flatness premise is added. Finite
coordinates and `e : ι ≃ Fin (n + 1)` retain the original dimension, including
zero, and the original common geometric universe. Existing omitted finiteness
binders remain exactly as in the original declarations.

The two named local standard derived-category instances are defined here
exactly once. Naturality and Sections locally activate those same constants;
they do not choose replacement models. All original definitions and proofs
are moved verbatim from the former coefficient owner.

## Status

This split leaf is source-reviewed preparation, not a compiled result. Native
acceptance remains pending. The family separation supplies incremental
boundaries; it is not a guaranteed memory repair or measured speedup.
