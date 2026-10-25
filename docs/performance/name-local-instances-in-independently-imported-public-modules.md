> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#name-local-instances-in-independently-imported-public-modules) · [Context](original-context.md) · [Case index](README.md) · [Previous record](pass-the-preservation-dictionary-of-an-equivalence-explicitly.md) · [Next record](hilbert-scheme-direct-images-compare-isomorphism-values-at-the-iso-level.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Name local instances in independently imported public modules

`local instance` controls instance search scope; it does not make its generated
constant name private inside a public section. Independent branches in
`Stalk/GeometricCohomologyDiagram.lean` and
`Stalk/GeometricLimitCohomologyCocone.lean` generated the same public HasExt
instance name. Each module compiled separately, but the shared native lint
and audit import failed in `remote-fe2c1151635345c6bc8467a75a2a441d`.

The repair gives the latter module's three local instances explicit,
module-specific names. Their types and bodies and the public theorem proofs
are unchanged. Exact source
`24f8f134a44294e235caadcbff5ddfe33e051fc37e97dd4ba05b3e857fb3ba99`
passed its sole changed frontend in
`remote-865a132c04aa463f8fe3faf4c559a3af`. The next shared import succeeded
and its audit covered 36,580 declarations; that run separately reported native
naming, documentation and simp-normal-form findings. Their five-source repair
and actual affected consumers then passed 23 frontends in
`remote-4a990481bbe1449cb6734161aca0c57a`. This uses retained compiler evidence
and the ordinary shared check, without replay or a separate diagnostic chain.

