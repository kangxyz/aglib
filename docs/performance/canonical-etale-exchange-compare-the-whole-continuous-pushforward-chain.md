> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#canonical-etale-exchange-compare-the-whole-continuous-pushforward-chain) · [Context](original-context.md) · [Case index](README.md) · [Previous record](horizontal-base-change-unit-prove-whole-mate-equations-abstractly.md) · [Next record](affine-limit-section-equality-type-the-isospec-arrows-and-section-values.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Canonical etale exchange: compare the whole continuous pushforward chain

EtaleDirectImageMate repeatedly exceeded the default kernel/isDefEq budget
when projecting a chain of direct-image composition and equality isomorphisms
onto concrete sheaf components. Individual component equations still forced
the kernel to normalize several large category carriers together.
Instead identify each original directImageComp hom/inv and equality transport
with its continuous-pushforward natural transformation at the whole functor
level. Compose there using a generic continuous-transformation chain lemma,
then evaluate only once. Supply the original composite-site continuity
instances explicitly. The final exchange proof uses the complete original
unit and site-square equations as typed inputs.
Graph127 accepted the full canonical EtaleDirectImageMate leaf in91 seconds
on37cce7b, without increased budgets or new mathematical premises. This closes
the original baseChangeMap identification, not merely existence of an iso.
The timing is ordinary compilation evidence, not a matched speedup claim.

