# Actual singular ancestors of a supported normalized chain

Source: [SingularAncestors.lean](SingularAncestors.lean).

Import `Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain.SingularAncestors`.
The namespace is `AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain`.

`singular_ancestor_properties_of_supported_rational_chain` retains the exact
OrdinaryStages original chain/support telescope: integral normal locally
Noetherian `X` of dimension at most two, an actual proper normalized-point
chain, and one original closed nongeneric `x` whose stalk is Nagata, rational
and of dimension exactly two. The original total restriction off `x` is an
isomorphism. Add one ORIGINAL singular terminal point `z` with `f z = x`.

For every native cut, its selected point is literally `c.fromTop i z` on
`c.stage i`. The theorem derives that this point is singular, closed and
nongeneric, its original stalk has dimension two and is Nagata and genuinely
rational, and its original prefix image is exactly `x`. No trajectory, later
singularity, closedness, dimension or rationality certificate is an input.

The proof first shows that an ordinary point-blowup stalk above a regular
original image stays regular. Away from the centre it uses the actual
restriction/stalk-map iso. At a regular dimension-two centre it uses the
native local regular-centre theorem, requiring no global regularity. For a
low-dimensional centre the original proper birational neighborhood theorem
identifies the same stalk. It does not assume all points of an open regular.

Accepted OrdinaryStages makes the LITERAL normalization arrow an isomorphism.
Its own stalk map transfers that regularity to the actual next stage. The
original normalization/blowdown triangle identifies its image; no replacement
point or residue map is chosen. Native `Fin.reverseInduction`, using the actual
`fromTop_step` equations, therefore forces every ancestor of the singular
terminal point to be singular.

At the final cut, `fromTop_last` is its genuine endpoint `eqToHom` iso. This
also handles a length-zero chain without silently identifying two different
supplied canonical embeddings. No embedding is introduced by this leaf.

Original prefix normality, Noetherianity and dimension then give closedness
and stalk dimension two by the generic normal-surface point theorems. The
actual total triangle supplies the prefix image equality. The genuine
ModelLocalization theorem over the ONE original rational stalk derives
Nagata and rationality of each selected original ancestor stalk.

Future canonical generation is needed only when such an actual ancestor
IS the selected step centre. This theorem asserts no generation, canonical
surjectivity, Gorensteinness, future full cone, regular terminal or resolution
existence. No child completion or finite-over-parent hypothesis is used.
