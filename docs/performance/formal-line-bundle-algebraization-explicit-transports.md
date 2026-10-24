> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#formal-line-bundle-algebraization-explicit-transports) · [Context](original-context.md) · [Case index](README.md) · [Previous record](nonflat-base-change-share-the-concrete-coefficient-constructor.md) · [Next record](site-cohomology-share-the-comparison-definition-not-only-its-proof.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Formal line-bundle algebraization: explicit transports

The positive-thickening isomorphism criterion in
[Formal/Algebraization/Detection](../../Aglib/AlgebraicGeometry/Modules/Invertible/Formal/Algebraization/Detection.lean)
encountered a deterministic `whnf` timeout at the standard 200000-heartbeat
budget while reporting a dependent `simpa` mismatch. The same attempt also
failed to synthesize `IsIso` through a composite pullback functor and through
the native adic-system inclusion. This was an elaboration/diagnostic failure;
the log does not establish a kernel-proof timeout or a compiler defect.

The retained repair makes each transport explicit:

- Name the iterated-pullback `IsIso` proof and pass it directly to
  `NatIso.isIso_map_iff`, rather than ask instance search to identify the
  composite functor's map.
- Rewrite the ideal-sheaf index with the single typed equality
  `K ^ n = idealThickeningIdealSheaf f (I ^ n)` before supplying the existing
  proof. Avoid simplifying the entire dependent `IsIso` proposition through
  the local abbreviation `K`.
- Supply the `IsIso` of the adic diagram's actual natural transformation
  explicitly before reflecting it through `adicSystemToDiagram`.

The affected declaration is
`isIso_of_positiveThickening_pullback_isIso`. Its statement and original
geometric maps are retained, with no heartbeat override. The ordinary scoped
build of `Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Algebraization`
then compiled both `Detection` and its rank-one consumer with no diagnostics.
The failed attempt is `remote-70faa5a11f2d47fd8616115436883985`; the successful
build is `remote-5f3f0f710ec04be4b365aad73b8fac39`, with source-content digest
`2a46c2ab76452bc5ee0f51d65b99ebb43c42a64a3a52350f84fe39fd0ab85e17`.
These are proof-iteration observations, not a controlled timing comparison.
The subsequent compatible-system effectivity consumer has its own build
coverage; this provider result does not certify that later assembly.

The native adic-system producer in
[Formal/System](../../Aglib/AlgebraicGeometry/Modules/Invertible/Formal/System/Adic.lean)
exposed a separate **kernel** conversion failure. At the actual ideal
thickenings, checking the quotient comparison followed by pushforward of
the successor isomorphism exceeded the same 200000-heartbeat budget. Separate
`rfl` projection formulas and an `asIso` of the explicit composite did not
repair it: even the optional equation expanding the concrete transition to
its literal unit-composite body timed out. Failed attempts include
`remote-46eed2bae8f24172b2f7f75b78885174` and
`remote-10b5c78e07f949b79766c12512b8b725`.

The effective boundary uses the same regular constructors on both sides.
`Data.adjointCoefficientMap` defines the original adjunction-unit composite
at variable maps and coefficients. `Adic.coefficientReductionMap` and its
isomorphism/unit laws are proved at variable ideal, closed immersion,
coefficients and coefficient isomorphism. The concrete `positiveTransition`
and `positiveReductionIso` specialize these shared definition heads directly.
They no longer assemble concrete composites separately and then require the
kernel to identify their expanded projections. The unnecessary expanded
concrete body theorem is omitted; the generic original-unit formula and the
native reduction-unit law remain proved.

The actual bundle/successor-isomorphism interface, original units, maps and
mathematical hypotheses are retained. The final producer and its original
geometric-reduction consumer compiled in
`remote-f34b91ce82b341c389a8f38d77043f41`, two fresh successful frontends with
no diagnostics, at source-content digest
`40f30a1a9c4eb71bf7b2722e20e300681bbe6e536b99470b9dab848e37edf9ad`.
No heartbeat increase or additional replay was used. This locates an effective
proof-representation boundary; without a kernel trace it does not identify
an internal compiler cause, and the changed declarations do not supply a
controlled speedup ratio.

