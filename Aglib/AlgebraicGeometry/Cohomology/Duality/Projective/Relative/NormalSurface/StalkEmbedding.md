# The original canonical stalk and its native numerator

For the existing embedded normal integral surface telescope, this leaf constructs
`normalSurfaceCanonicalStalkEmbedding` into the ORIGINAL `X.functionField`.
Every point uses the ONE `normalSurfaceCanonicalGenericFrame`, and the explicit
germ theorem retains that frame's value on the original generic germ.

Finiteness is derived from finite presentation and the actual local-spectrum
sections isomorphism, with no added Noetherianity assumption on a later base.
That finiteness theorem itself requires only Noetherian R, the original finite
projective embedding and its actual finite-coordinate equivalence. The full
canonical telescope derives torsion-freeness from existing canonical scalar
regularity, injection from the accepted generic stalk embedding, and
nontriviality from full support. No singular Gorenstein, rank-one, canonical
frame, rationality or finite-over-original-parent premise is supplied.

`normalSurfaceCanonicalStalkFractionalImage` and
`normalSurfaceCanonicalStalkEquivNum` are thin calls to the unique native
`FractionalIdeal.FiniteEmbeddedModule` construction. The exact original law is

```
algebraMap S X.functionField (e m : S) = I.den • F m.
```

The germ-specialized law and nonzero numerator follow from the same maps and
full support. No independent ideal or denominator construction, choice-
independence theorem, tautological quotient, kernel argument or Gorenstein
modification is asserted. The exact `bdd746` source passed its own native check in graph 120 (4.4 s).
The graph later stopped at an unrelated resource guard; the individual pass
and unchanged posthash were retained in compiler snapshot 131. No repeated
check or whole-graph success is claimed.
