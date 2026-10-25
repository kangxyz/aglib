> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#retain-native-localization-structures) · [Context](original-context.md) · [Case index](README.md) · [Previous record](retain-the-original-map-in-ideal-power-comparisons.md) · [Next record](preserve-both-affine-unit-comparisons-in-tensor-section-transport.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Retain native localization structures

With Lean 4.34.1 and Mathlib `d13f23b`, the generic-ring comparison in
[ArcTermination](../../Aglib/RingTheory/Blowup/ArcTermination.lean) encountered
a native `OreLocalization.instSemiring` versus fresh `CommRing` projection
mismatch, with an unexposed `OreLocalization.instAdd` in the diagnostic.
Its generic quotient-map specialization also exhausted 200000 heartbeats
at `isDefEq`. Source
`d98b1c8f0e6640f4f6843ace2b34d7bedba208728b4d2e18ecd410a703b03528`
recorded these failures in `remote-1f49812de3c9446db53b7f46d94f6bd4`.

The retained repair names the literal native localization with a regular
`arcGenericLocalRing` definition and exposes its native ring, algebra,
localization and local-ring instances consistently. Chart-map uniqueness
uses its sufficient semiring target. One `genericQuotientLift f S`
constructor serves both generic rings, and the comparison receives the
same actual ring homomorphisms into an abstract target. It no longer
converts between independently instantiated literal quotient maps.

Source `f69d9776e231497a5951eac41d27ae67c6ab564cacd230c4bf78ce14925d4720`
passed the complete module in 47 seconds in ordinary native run
`remote-4da3d88998fa431d8ee02bfe0cd45601`, with unchanged premises, maps
and default budgets. This removes the reported failures on that snapshot;
it is not a controlled speedup or compiler-defect diagnosis. The outer
graph failed elsewhere. Later minimal-generator and termination extensions
have separate source identities and coverage; full arc termination was
not proved by this pass.

