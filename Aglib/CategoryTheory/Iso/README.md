# Equality transport of isomorphisms

[Composite](Composite.lean), imported as `Aglib.CategoryTheory.Iso.Composite`,
adds `CategoryTheory.Iso.mpr_hom`: transporting an isomorphism endpoint along an
equality gives the original forward map followed by the canonical `eqToHom`.
The isomorphism and equality are the actual categorical inputs.

Cancellation and reassociation use Mathlib's existing `Iso` and `Category.assoc`
API. The historical cancellation and five-map bookkeeping wrappers have no
parallel native constants.

[CertifiedHomTransport](CertifiedHomTransport.lean) gives
`CategoryTheory.certifiedHomTransport_val` for a morphism packaged with a
proposition-valued certificate. Transporting the target index transports both
the morphism and its certificate; the underlying arrow is the original arrow
followed by `eqToHom` for the target equality. It works in any category. The
[affine modification comparison](../../AlgebraicGeometry/Cohomology/GrothendieckExistence/AffineModificationComparison.lean)
uses this formula to retain its original certified maps.
