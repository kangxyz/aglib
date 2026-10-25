> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#bounded-presentations-preserve-typed-section-transport) · [Context](original-context.md) · [Case index](README.md) · [Previous record](reindexed-direct-image-comparisons-evaluate-a-whole-identity-first.md) · [Next record](convert-the-coefficient-family-before-specializing-the-canonical-exchange.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Bounded presentations: preserve typed section transport

Affected declaration:
`AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.BoundedPresentation.generators_isSeparating`
in `Constructible/TorsionColimit/BoundedPresentation.lean`.

Private basis 2c34f185fa859e862661f939cd216b07bcccfb26; Lean 4.34.1;
Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.

The first module version, SHA256
32ae530eddea5ee1ebadae05f910fe0925be79ff51b35986fbb9d9835ea36f39,
exhausted the standard 200000 elaborator heartbeats at `whnf` in
remote-4f8d706226d14488959cf43eb95b836d, source snapshot
1c8814701ec3705c9023b2f01a9f106b309d7c0f8c90f062e6727655851dedd2.
The generated downstream unknown
`generators_isSeparating` diagnostic was cascading; no endpoint from that
module was admitted by the failed run.

The repair first uses the actual single-index constructor of
`ObjectProperty.ofObj`, rather than trying to treat it as an existential
pair. The subsequent section calculation keeps the original free mod-n
cokernel carrier behind the named `sectionsEquiv` boundary. A typed
`sectionsEquiv_symm_naturality` equation transports the actual coefficient
arrow on an unchanged section. The proof composes these exact equations
instead of simplifying the concrete affine restriction and free-cokernel
carrier. Native reflection-of-isomorphism instances are installed at their
fully typed original maps. The final filtered presentation also uses the
actual costructured-arrow category and its explicit standard-universe
`SmallModel`, with essential smallness proved from the finite-colimit closure.

The unchanged mathematical construction uses actual sheaves killed by n,
original free ZMod representables on affine etale tests, the original
coefficient maps, and the original underlying colimit cocone. No constructible
presentation or finite cogenerator premise was added; stages are still only
proved to belong to the genuine finite-colimit closure. No heartbeat or
resource ceiling was raised.

Actual successful scope: exact BoundedPresentation module SHA256
 d07e613bffcdd8d1d38887ad81e02435466e9643ed0a1acd420f6bb51cba66ec,
accepted as one frontend in remote-0ee44936a46b4f95b2601122b7c5763e,
source snapshot 6fb90108db4177e899d229330ed65e1e9106c7d31be7f96167cd86df3e98db3c,
reported 6.2 seconds, standard 200000, no diagnostics in that leaf. The same
invocation accepted Sections and failed the separate Bounded leaf; this
records only BoundedPresentation coverage. These are ordinary existing
proof-iteration observations, not a controlled benchmark or a diagnosis of
a Lean defect. No additional profiling, replay, audit, or benchmark was run.


