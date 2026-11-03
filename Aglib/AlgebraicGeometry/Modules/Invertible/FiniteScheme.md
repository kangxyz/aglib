# Lines on finite field schemes

Source: [FiniteScheme.lean](FiniteScheme.lean).

Five original numerical helpers are owned here, shared by coefficient-curve
quotient dimensions and the anticanonical Hilbert calculation. Their original
names and namespace `AlgebraicGeometry.Scheme.Cohomology` are preserved.

A line on a semilocal affine scheme is trivial by the native affine Picard
comparison. A scheme finite over a field has an Artinian coordinate algebra,
so the same existence statement applies to its full possibly nonreduced
structure. Transporting this isomorphism through the actual global-sections
or pushforward/cohomology functor proves equality of dimensions with the
structure module, for its original structural field action.

The trivialization is used only inside numerical proofs. It is not a chosen
orientation and never identifies a coefficient line with the ground field.
No reducedness, algebraic closedness, or separability hypothesis is imposed.
Source provenance: these line comparisons were extracted from the original
coefficient-curve QuotientDimension helpers. They use the same full finite
scheme and do not import canonical-generation or surface geometry.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/CohenMacaulayCurve/AnticanonicalHilbert](../../Cohomology/Duality/Projective/Relative/CohenMacaulayCurve/AnticanonicalHilbert.md).
