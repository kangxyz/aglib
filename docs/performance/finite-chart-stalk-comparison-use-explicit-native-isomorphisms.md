> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#finite-chart-stalk-comparison-use-explicit-native-isomorphisms) · [Context](original-context.md) · [Case index](README.md) · [Previous record](affine-limit-section-equality-type-the-isospec-arrows-and-section-values.md) · [Next record](resized-cohomology-diagrams-stop-extensionality-at-the-actual-group-element.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Finite chart stalk comparison: use explicit native isomorphisms

The monolithic GlobalEvaluationChart proof in graph129 exceeded the native
memory limit. Splitting the actual index, chart stalk comparison and coordinate
identity exposed a further kernel timeout in ChartStalkComparison graph130:
`asIso` of the stalk image of the canonical exchange required normalization of
its inferred IsIso instance and inverse.
Use the original nativeStalkIso.app and the explicit
sheafFiber.mapIso(etaleBaseChangeIso.app), then prove a complete hom boundary
using the original nativeStalkIso_hom and etaleBaseChangeIso_hom equations.
Graph131 accepted ChartStalkComparison in2.4 seconds, the coordinate leaf in
2.2 seconds and GlobalEvaluationChart in1.0 second. Memory/heartbeat ceilings,
mathematical hypotheses and canonical maps were unchanged. No extra replay,
audit or matched performance benchmark was run.

