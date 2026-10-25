> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#preserve-both-affine-unit-comparisons-in-tensor-section-transport) · [Context](original-context.md) · [Case index](README.md) · [Previous record](retain-native-localization-structures.md) · [Next record](retain-the-original-pullback-row-equation-boundary.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Preserve both affine unit comparisons in tensor-section transport

On the pinned Lean 4.34.1 / Mathlib `d13f23b7` basis, the actual affine
presentation row in
[AffineRow](../../Aglib/AlgebraicGeometry/Blowup/ProjectivePresentation/AffineRow.lean)
exhausted 200000 elaborator heartbeats at `whnf` in
`pulled_tilde_spanSingleton`. Keeping the same unbundled module carrier at
every occurrence was insufficient (`remote-fc6fcc504e1e44568d2087416ccce62b`).
Carry both original `tildeSelf` comparisons explicitly. In particular the
source unit is transported by the actual pullback of `tildeSelf R` followed
by `pullbackUnitIso`; the proof no longer asks a concrete specialization to
identify pullback of the associated scalar module with pullback of the unit.

Concrete map-identity and unit congruence pastes then moved the timeout to
`affine_tilde_unit_triangle` (`remote-80e660ecc8564cbc93647fae9ed5ffa7`).
The successful boundary proves `unit_triangle_of_id` over an abstract functor,
with the actual unit arrows and their identity equations as parameters. A
single specialization uses the existing proved
`affinePullbackTildeIso_unitToUnit`. The original unit maps, full tensor ideal,
section reconstruction and epimorphic presentation remain the actual objects;
the equations are proved witnesses, rather than additional assumptions.

Exact Row source `a1b35d34009edc8eac0bf5f52c357e7fcd821f749c322117699a2c9b89bbcd2f`
compiled in 72 seconds in `remote-1e5790e91c584985854cb1ff33475be9`, source
snapshot `af9e59a97a25c21887eeee4ac29ff44ef8843e54dd01c4824de227bcec667a6b`,
under the unchanged 200000-heartbeat budget. No opacity, trust, premise or
resource-cap change, profiling or extra replay was used. The chart consumer
failed separately in that graph; this evidence covers Row, not the completed
projective embedding. Changed sources and failed baselines do not establish a
controlled runtime improvement.

