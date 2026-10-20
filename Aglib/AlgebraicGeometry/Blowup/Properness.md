# Properness of every locally Noetherian universal blowup

`Properness.lean` supplies the exact original family `NoetherianBlowupProper`
through `Scheme.Blowup.noetherianBlowupProper`. The statement concerns an
arbitrary locally Noetherian scheme, its actual ideal sheaf and any given
universal representative. No existence, atlas or properness family is assumed.

On `Spec A` for a Noetherian ring `A`, `spectrumDatum` has the already proved
proper native Rees Proj map. The existing unique comparison transfers properness
to every given universal representative (`BlowupDatum.isProper_of_spectrum`).

For a locally Noetherian base, an actual affine open cover has Noetherian
coordinate rings. The proved `flatPullbackDatum` is the literal pullback of the
given representative to each cover member, for the actual inverse-image centre.
These pullbacks are proper by the affine result. Native Zariski locality of
properness at the target then proves
`BlowupDatum.isProper_of_isLocallyNoetherian`.

This proof is independent of the new global existence construction. The focused
client also combines properness with `blowupDatum` to obtain an actual proper
universal representative. All Noetherian premises and original maps are retained;
source-bound compilation receipts are separate from this guide.
