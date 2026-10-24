# Instances and universes

Return to the [performance lookup](../PERFORMANCE.md).
Distinguish expensive search, an underconstrained universe and a genuinely
missing structure. Similar timeout messages do not make them the same problem.

## Supply an existing dictionary at its actual type

Bind repeated universal proof instances locally, pass an existing finite-index
witness directly, or use `inferInstanceAs` at the required `HasExt` type.
When an equivalence already proves preservation, obtain the relevant dictionary
from that equivalence's adjunction and project its field. Use
`IsIso.mono_of_iso` when precisely that hypothesis is available.

For `genuinePresentationCoconeIsColimit`, implicit search for preservation
under `scalarLift X n` reached the 20,000 synthesis limit. Passing the
equivalence's preservation dictionary to the original cocone repaired the
leaf; the exact source was recorded as passing in 6.1 seconds. A separate
child in that graph still failed.
[Original preservation case](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#pass-the-preservation-dictionary-of-an-equivalence-explicitly).

Quillen's [vector-bundle case](https://github.com/kangxyz/quillen-k-theory/blob/main/docs/performance/local-cases.md#vector-bundle-instance-inference)
provides a matched local comparison for reusing universal instances and the
existing finite-index witness. These are restricted uses of proved instances,
not permission to add assumptions or change global instance priorities.

## Fix the category before dependent universe synthesis

An explicit universe on the final theorem can be too late. Give the category,
native structure or preservation instance its actual type before dependent
inference. In particular, retain independent Ext, site, scheme and
derived-category universes rather than imposing an equality for convenience.

The small-model/sheafification repair bound
`smallCategorySmallModel : SmallCategory.{max u v}` before dependent
sheafification/Grothendieck synthesis. Separate Kan-preservation cases selected
the exact `ModuleCat` limit/preservation instance for the actual shape.
[Small-model case](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#site-cohomology-share-the-comparison-definition-not-only-its-proof),
[Kan-extension universe case](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#pinning-the-actual-module-universe-in-a-kan-extension-preservation-proof),
[bounded presentations](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#bounded-presentations-preserve-typed-section-transport).

These solve particular underconstrained expressions; they do not justify
monomorphizing a public API.

## Keep native parent structures and scalar actions

Use the supplied localization ring, module action, grading and comparison map
throughout the calculation. A separately projected `CommRing`, Ore-localization
structure or grading can be incompatible at the relevant boundary even when
its underlying objects look the same.

The [native-localization](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#retain-native-localization-structures)
and [exceptional-chart grading](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#retain-the-given-grading-in-an-exceptional-chart-quotient)
cases retained the original structures before concrete specialization.

Underlying functors agreeing does not make their supplied `CommShift`
coherences identical. The native-shift case also needed an actual missing
provider import; generic composition helpers alone did not supply that
mathematics.
[Original shift/coherence repair](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#keep-native-shift-structures-explicit-in-the-canonical-exchange-proof).

## Request only the structure the argument uses

Use the native additive `Ext.precompIsoAddEquiv` when a linear integer-module
structure adds an irrelevant diamond. Use sized `Subobject.sInf` rather than
synthesizing an unused complete lattice. When a known native isomorphism or
field point is available, use it directly instead of rebuilding `asIso` or a
generic structure.

[Additive Ext example](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#additive-ext-transport-avoid-an-irrelevant-integer-module-diamond),
[native sized infima](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#use-native-sized-subobject-infima-instead-of-rebuilding-a-concrete-lattice).
The native interface must satisfy the original mathematical conditions. These
are targeted interface choices, not evidence that every stronger structure is
slower.
