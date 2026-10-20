# Closed ideal sheaves and their actual subschemes

These leaves extend Mathlib's `Scheme.IdealSheafData`; they do not introduce a
second ideal module or closed-subscheme object.

- [Comaximal](Comaximal.lean) derives comaximality from disjoint actual supports
  and proves the comaximal sum/intersection identity using ideal multiplication.
- [IntersectionComparison](IntersectionComparison.lean) constructs actual
  intersection isomorphisms from equality of pullback ideals, or equality modulo
  the actual kernel of a morphism. It retains both projections and the `Over`
  base triangles. This comparison needs no reducedness assumption.
- [MonoFactor](MonoFactor.lean) identifies the inverse-image kernel of a closed
  immersion factoring through a monomorphism.
- [OpenRestriction](OpenRestriction.lean) proves open pullback of actual kernel
  ideals and finite intersections. The kernel statement keeps quasi-compactness.
- [SpecKernel](SpecKernel.lean) identifies the actual global kernel ideal of a
  spectrum map through the canonical global-sections isomorphism.
- [RadicalSubscheme](RadicalSubscheme.lean) derives reducedness of the actual
  subscheme from radicality of its ideal sheaf.
- [ReducedClosedUnion](ReducedClosedUnion.lean) proves radicality of the kernel
  of a quasi-compact map from a reduced source and identifies a reduced closed
  union with the intersection of its actual component kernels.
- [ReducedFactor](ReducedFactor.lean) constructs factorization of a map from a
  reduced scheme into a closed subscheme from actual image containment.
- [ReducedComparison](ReducedComparison.lean) compares reduced closed schemes
  with equal support, including open restrictions. Its intersection comparison
  requires reducedness of the actual larger intersection; reducedness of its
  ambient scheme is not substituted for that condition.
- [TwoPointSubscheme](TwoPointSubscheme.lean) proves that every ideal of a product
  of two fields is radical, and every actual closed subscheme of that spectrum
  is reduced.

Most declarations extend `Scheme.IdealSheafData`. The closed-comparison APIs
belong to `Scheme.ReducedClosedSubscheme` and
`Scheme.ReducedClosedIntersection`; the two-point facts belong to
`Scheme.TwoPoint`. `AlgebraicGeometry.liftReducedToClosed` is the canonical
factorization reused by the comparison. The gluing and curve construction
families consume these leaves. Source identities appear in their headers.
