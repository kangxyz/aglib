# Original inverse-trace section surjectivity

Source: [Generation.lean](Generation.lean).

Import:
`Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.Generation`.

`ordinaryTracePullback_app_top_surjective` proves surjectivity on global
sections of the existing `ordinaryTracePullback f τ` for any actual invertible
trace map `τ : f_* M ⟶ N`. It uses the original counit factorization and the
native evaluation functor on module sheaves.

`ordinaryTracePullback_baseChange_app_top_surjective` proves the same statement
for the literal pullback of that map along the first projection of an actual
Cartesian square. Its hypotheses are exactly flatness of the base-change map,
quasi-compactness and quasi-separatedness of `f`, quasicoherence of `M`, and
invertibility of the original `τ`. The existing
`canonicalTraceOrdinaryBaseChange_isIso` makes the original ordinary mate an
isomorphism; `ordinaryTracePullback_baseChange` identifies the actual map with
isomorphisms followed by the original counit. It does not assert that arbitrary
pullback preserves surjectivity on global sections.

No canonical object, derived realization, trace map or Cartesian square is
reconstructed. There is no parent frame, child Gorenstein, curve generation,
finite later-stalk algebra, or complete later-stalk premise. In the surface
consumer, invertibility of the actual canonical trace is provided separately
from the original derived unit. Arbitrary-field exceptional-curve generation
remains a distinct the coefficient-generation argument obligation before canonical evaluation epimorphy.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/Trace/PointBlowupGeneration](PointBlowupGeneration.md).
