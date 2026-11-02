# Original transpose evaluation under pullback

This lower owner contains the unchanged original `pullback_transpose_dualEvaluation`
producer and its single private categorical comparison proof, formerly owned by
`Surfaces/RationalSingularities/IntegralTrace/PullbackTransposeEvaluation`.
The old module is a thin public import, so its original consumer and public
qualified theorem name remain unchanged.

The original coefficient from a line to the structure module is transposed,
pulled back, and preceded by the inverse original structural-unit comparison.
The native pulled-back dual evaluation recovers the original pulled coefficient.
The proof uses only native tensor naturality, the original unit comparison,
and the original transpose/evaluation equation. Its two imports, universe,
telescope, scoped options, and proof commands are retained unchanged.

`DualMapToPullback` uses this law with the existing perfect-pairing equivalence
to transport original transpose sections; it is a separate focused leaf so
existing evaluation consumers do not acquire that new leaf's imports.

Current relocated source
`505bd579e454b0cf68bb54251eaa981dec5775bfec1fcc2db6cca2510cfe9cca`
passed normal whole-owner check own173: 3.5 seconds at the leaf, 53.060 seconds
total, exit 0 with no resource guard. This is evidence for the moved original
producer at its new path, not transferred acceptance from the old owner or a
downstream geometry theorem. The old compatibility import and higher consumers
are not covered by this check.
