> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#construct-the-tensor-comparison-inside-the-shared-chart-witness) · [Context](original-context.md) · [Case index](README.md) · [Previous record](cache-independent-chart-producers-before-concrete-geometry.md) · [Next record](what-the-measurements-establish.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Construct the tensor comparison inside the shared chart witness

The actual scalar Rees-chart triangle in
`Blowup/ProjectivePresentation/ScalarChart` exhausted the default 200000
heartbeats after the independent chart producers had compiled. Sharing only
`ChartTriangleEq` at the public producer and consumer still failed in
`remote-cd0528cad14b4f25bbce7027db079eae`. The first shared arrow witness
also failed in `remote-c854a529f942462a9cb03811e9b9e91d`: its Rees
specialization compared an independently constructed scalar `RingEquiv`
with the generic witness's expected tensor/localization types. That source
also contained an unavailable private-helper reference.

The successful `gradedChartArrowWithEquation` takes the original Away
algebra equivalence and constructs the actual tensor ring comparison
inside the generic constructor. It proves the coefficient square there,
pastes the native Cartesian chart square with the public Spec-square
lemma, and returns the actual chart arrow together with its literal value
equality and original scalar-map triangle. `scalarChartToProjData`
specializes this one constructor; the public arrow and both proofs project
the same witness. The actual chart-frame and augmentation consumers retain
the value equality as well as the projection triangle. The full tensor
Rees algebra, original row and geometric hypotheses are preserved.

In `remote-d74407bf6e1847f1842de9dd12c41ae9`, source snapshot SHA-256
`d3d754cb7deb6ce97d26c4d6c8e04cc3bada9c21145f064c9de64c3a62e9d8fa`,
`ScalarChart.lean` SHA-256
`a6306d446833da8fded31f22e9fb03b5ddd0b8c113543fcac649dacda2e63db4`
compiled in 128 seconds and its actual `ChartCoordinates.lean` consumer
SHA-256 `b5c032224be360aeece4818bd5902d82cac0dddf1e203d522a205ab637f4e378`
compiled in 113 seconds. Both used default heartbeat/synthesis budgets and
unchanged resource ceilings. This reuses ordinary proof-iteration evidence;
no profiling, replay, separate client run or controlled benchmark was added.
The whole Proper graph then failed in the newly reached `Embedding` module
on separate interface and instance errors, so this records the chart and
coordinate passes only, with no general-contraction completion claim.

The subsequent `Embedding` repair also keeps the complete restriction
comparison generic over the affine square and framed family before its
concrete section-ring specialization. It passes the existing epimorphism
proof explicitly to the original finite-family constructor. Unused finite
section instances are omitted only from the two private comparison lemmas;
the public finite embedding retains its needed finiteness hypotheses.
With `Embedding.lean` SHA-256
`27535326e5c4d925a4ff795cf112cca76cccbeb5d861395e949551ddb5148c22`,
run `remote-37836972b3b9498cb3ef9168b5fd58bd`, source SHA-256
`1ac63637a49c93bd5e981518ed64c89557b727966ac47f3119b739fd383332a8`,
compiled that module in 149 seconds and the original forward chain in
9.1 seconds at the standard budgets. That parent run then failed a
redundant rewrite in the upper projectivity assembly. Removing the rewrite
preserved the same base triangle. The final whole-Proper run
`remote-7ac9858abc3849a7bf9112dbadcdb71b`, source SHA-256
`ce5280f7f3740db61928d11a8fb9a2862efb26af108bc6bc9241510765251494`,
exited zero, compiling `Surfaces.Projectivity` in 7.6 seconds and
`Surfaces.Contraction.Proper` in 11 seconds. These are ordinary incremental
build observations; no controlled timing ratio or broader library checks
are inferred from them.

