> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#keep-the-original-universal-exchange-test-at-a-shared-data-head) · [Context](original-context.md) · [Case index](README.md) · [Previous record](keep-native-shift-structures-explicit-in-the-canonical-exchange-proof.md) · [Next record](use-a-finite-original-unit-calculation-for-constant-direct-image-coordinates.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Keep the original universal exchange test at a shared data head

Basis: Lean 4.34.1, Mathlib `d13f23b`, and the published proper-reduction
suppliers retained at `f464f6b`. The first
[universal-property](../../Aglib/AlgebraicGeometry/EtaleCohomology/Proper/Universal/Basic.lean)
source, SHA256
`e55d71f9f83faeca6b0e1ce20a0eeede7e3f61bf303a02c43c5e1da0e975428a`,
failed in `remote-6260a813bb0f4c8e91ea0dcd44ab8a90`. Its actual
surjective-descent declaration exhausted the kernel's deterministic budget;
other diagnostics concerned concrete pullback transport and implicit object
quantifiers. No budget was raised.

The repair defines one regular `boundedExchange` predicate for the original
all-degree, all-n-killed-coefficient test. Generic composition and descent
helpers consume and return that same head before actual Cartesian squares
are supplied. In composition, the actual pullback triangle is retained by
`clear_value a` and substitution of its original equation before applying
the generic helper. Explicit theorem applications preserve the entire
implicit object quantifier in universal finite membership and descent.
The original exchange maps, coefficients and hypotheses are unchanged.

Final source
`7a56a974fbf33818e1b21f54654a9c68c705cbb2ce939a92254af797569cbf1f`
passed the complete leaf in `remote-0b94a03fbf9447e1a503ae0b5cf1097e`,
with one successful frontend and 9.64 seconds for the remote build action.
This reuses ordinary compiler evidence; it establishes removal of the
observed timeout, not a controlled speedup or a compiler-defect diagnosis.
The separately compiled model transport retains four independent model
universes; final projective-line exchange is still a mathematical input.

