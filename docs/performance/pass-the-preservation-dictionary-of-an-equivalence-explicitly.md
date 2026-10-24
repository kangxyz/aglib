> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#pass-the-preservation-dictionary-of-an-equivalence-explicitly) · [Context](original-context.md) · [Case index](README.md) · [Previous record](retain-complete-product-families-through-finite-stage-factorization.md) · [Next record](name-local-instances-in-independently-imported-public-modules.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Pass the preservation dictionary of an equivalence explicitly

In [GenuineModules](../../Aglib/AlgebraicGeometry/EtaleCohomology/Constructible/PositivePresentation/GenuineModules.lean),
`genuinePresentationCoconeIsColimit` transports an original cocone through
canonical scalar conversion, an actual equivalence. In
`remote-2f45842a61de4ea99587e88fe0e0f568`, implicit synthesis of
`PreservesColimit D (scalarLift X n)` reached the standard 20000
instance-search heartbeat limit at that declaration.

The repaired proof obtains `PreservesColimitsOfShape I (scalarLift X n)`
explicitly from the equivalence's adjunction, projects its
`preservesColimit` dictionary, and applies the dictionary's `preserves`
field to the original colimit. Extension by the original `canonicalModuleIso`
retains the point and literal underlying cocone equations. No global instance
or heartbeat change is required.

Exact source `92e86ad7a778777b15dff05050c4c6ef72b83d89690aef793c0c8d321986a2b5`
passed in `remote-3d9b7fc4a13f4c429e8fbc0df4b09070` (6.1 seconds reported).
That graph also contained a failing separate AffineRestriction child; only
this passing leaf is credited. These retained observations validate the
repair, not a controlled speedup or a profiling experiment.

