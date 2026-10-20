# Effective epimorphisms over a base

`Over.lean` constructs ordinary morphism descent in `CategoryTheory.Over S`
from the actual underlying effective epimorphism. Its cocycle reduction,
`effectiveEpiDesc`, factorization equation, and `effectiveEpi_of_left` theorem
retain arbitrary category and morphism universes. The descended underlying map
is literally the canonical `CategoryTheory.EffectiveEpi.desc`.

The current scheme consumer is
[`Group/EtaleQuotient`](../../AlgebraicGeometry/Group/EtaleQuotient.lean), which
uses Mathlib's effective epimorphism for a given etale surjection. No quotient
scheme, cover, or application isogeny is supplied by this categorical theorem.
