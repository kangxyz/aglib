# Literal normalized presentation of the original ordinary chain

`PointBlowupChain.exists_normalizedPresentation` takes an actual ordinary chain
`c : PointBlowupChain g`, integrality of its original base X, and genuine
`c.NormalStages`. It returns a literal normalized-point chain `d` on `f:Z→X`,
an explicit `E:T≅Z` from the original ordinary terminal, exact equality of
lengths, and the original structural triangle `E.hom ≫ f = g`.

Only post-blowup stages must be normal. There is no normality condition on X,
and no Noetherian, proper, Nagata, global dimension, regular-terminal,
finite-normalization, completion or rationality premise. The actual local
dimension-two centres are already part of the ordinary chain and exclude
its generic points.

The proof inducts on the existing chain. For its original first ordinary
blowup B, actual normality makes the literal generic normalization arrow
`nu:N→B.Y` an isomorphism. The existing normalized tail is transported along
`(asIso nu).symm` by `NormalizedPointBlowupChain.transportIso`. Its terminal
isomorphism composes with the inductive terminal isomorphism; the original
triangle follows by associativity and cancellation of `inv nu ≫ nu`.
The native cons operation adds exactly one to the retained length.

The output Z is the forced native normalized presentation, not an arbitrary
replacement model. It is not identified with T by scheme equality, and the
statement does not falsely claim a normalized-chain witness on literal g.
Later regularity and unchanged-open comparisons use the explicit E and its
triangle. Existence of an ordinary resolving chain and its genuine normal-stage
invariant remain obligations of the geometric producer.

The exact initial source `a02f4fd9d10e8a151559bf479a639244cdb13e6622367f4b9972e30fe4edd5ab`
passed its own native selected check in recovery graph 68 (2.2 seconds,
2026-10-31), after its actual NormalStages provider passed. This is an
individual leaf result, not success of every unrelated graph target.
