# Actual finite projective-product geometry

The focused import is `Aglib.AlgebraicGeometry.ProjectiveSpace.Products.BaseChange`.
`AlgebraicGeometry.ProjectiveSpace.productBaseChangeIso` is the existing
`Scheme.finiteProductOverPullbackIso`, viewed through native pullback
symmetry and the original forgetful functor from `Over S`.
It identifies the base-first fibre product with the same native finite
product of the original component pullbacks. No alternative product
scheme or projectivity predicate is defined.

The forward map retains the original first projection to the new base
and every original component projection to its polynomial projective
space. For the empty family it is literally the original first
projection of the pullback of the identity. These comparison statements
need no finite-coordinate, Noetherian or flatness hypothesis.

With finitely many coordinates in each factor, the original product
projection is proper. Over a locally Noetherian new base, its original
fibre product is locally Noetherian. The original presentation ring is
arbitrary. The
[cohomology product family](../../Cohomology/Projective/Products/README.md)
uses this comparison to connect the actual graph-product pair to the
already proved native projection tower.
