# Finite fibres of proper birational morphisms

Import `Aglib.AlgebraicGeometry.Morphisms.Proper.QuasiFinite`.

For integral schemes `X` and `Y`, let `f : X ⟶ Y` be proper and dominant.
Assume `NormalStalks Y` and that the original
`CommRingCat.ofHom (functionFieldMap f)` is an isomorphism. Then every point
`y : Y` with finite actual point fibre `f ⁻¹' {y}` has an open neighborhood
`U : Y.Opens` for which the original restriction `f ∣_ U` is an isomorphism.

The declarations in `AlgebraicGeometry.Scheme` are:

- `exists_isIso_restrict_of_isProper_birational_of_finite_preimage_singleton`:
  the finite-fibre conclusion above.
- `exists_isIso_restrict_of_isProper_birational_of_quasiFiniteAt_fibre`:
  the same conclusion when `f.QuasiFiniteAt x` holds for every `x` satisfying
  `f x = y`.

Neither result assumes local Noetherianity or normality of `X`. Birationality
concerns the supplied morphism and its actual function-field map, rather than
an unrelated birational equivalence between the two schemes.

## Proof and suppliers

The pinned Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`
already proves `IsFinite.of_isProper_of_locallyQuasiFinite` in
`Mathlib.AlgebraicGeometry.ZariskisMainTheorem`. Its
`exists_isFinite_morphismRestrict_of_finite_preimage_singleton` supplies a
finite restriction around the given finite fibre: properness makes the image
of the complement of the quasi-finite locus closed. This file directly
reuses the finite-fibre neighborhood theorem; proper quasi-finite finiteness
is its native supplier.

[BirationalFunctions.lean](BirationalFunctions.lean) supplies
`AlgebraicGeometry.Scheme.isIso_c_of_isProper_birational`, which identifies
the actual structure-sheaf map of `f`. On the finite neighborhood, the morphism is
affine. The native affine isomorphism criterion applies on every affine open
of that neighborhood. The formula `morphismRestrict_app` identifies its section
map with the original section map followed by the canonical identification
of the corresponding inverse-image open. Thus the resulting isomorphism is
the original restricted morphism.

For the second result, the native singleton criterion for `QuasiFiniteAt`
makes the actual fibre discrete. Properness makes it compact, so it is finite
and the first result applies.

The consumer is the finite-fibre step in the proper birational isomorphism
locus used by the surface factorization program. These results supply local
isomorphism neighborhoods; they do not construct a surface contraction or a
factorization into blowups.
