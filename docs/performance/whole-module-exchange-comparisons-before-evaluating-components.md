> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#whole-module-exchange-comparisons-before-evaluating-components) · [Context](original-context.md) · [Case index](README.md) · [Previous record](test-dependency-handoff-and-native-resource-limits.md) · [Next record](generated-import-entries-and-file-length-limits.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Whole module-exchange comparisons before evaluating components

The 2026-10-24 exceptional-image source integration retains several validated
repairs on Lean 4.34.1 with the pinned Mathlib. In
[`ModuleSourceExchange`](../../Aglib/AlgebraicGeometry/EtaleCohomology/Exceptional/Open/ModuleSourceExchange.lean),
the original source-square component exhausted the kernel budget when its
native isomorphism chain was expanded inside the component calculation.
The passing proof first identifies the complete original isomorphism, then
evaluates it through an abstract component lemma and the original adjunction
hom-equivalence. The recorded failed graph is source-pasting-122; the
source-normalization-124 producer passed in 42 seconds.

For
[`ModuleCartesianExchangeMate`](../../Aglib/AlgebraicGeometry/EtaleCohomology/Exceptional/Open/ModuleCartesianExchangeMate.lean),
an opaque arrow chase alone did not remove the memory failure in graphs
136--138: conversion of native comparison aliases through `hom.app` remained
expensive. The successful proof establishes equality of the two whole
Cartesian comparison isomorphisms and transports a proposition in those
parameters through an abstract theorem. The final original-mate equality is
obtained by transitivity. The recorded Cartesian-mate-139 producer passed
in 13 seconds.

These repairs preserve the native units, counits, comparisons and actual
exchange. They add no invertibility premise and change no resource cap or
transparency option. The reported times and failures are ordinary historical
producer evidence, not a controlled speed comparison or a unique attribution
of compiler cost. Exact source versions and individual compiler results are
preserved with the integration intake. A nonzero outer-graph exit does not
invalidate an unchanged module's recorded successful frontend.

When categorical `map_id` fails at a literal identity, use the concrete
functor's `.map_id` or qualify `CategoryTheory.Functor.map_id`: an unqualified
name can resolve to the unrelated root functor law. For an apparently
reflexive native component equation, fix the entire original arrow and its
carrier before applying typed congruence or composition laws. Do not replace
the original maps by assumed normalized ones.

