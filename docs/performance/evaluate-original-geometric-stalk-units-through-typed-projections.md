> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#evaluate-original-geometric-stalk-units-through-typed-projections) · [Context](original-context.md) · [Case index](README.md) · [Previous record](augmented-amitsur-differentials-and-typed-tensor-coordinates.md) · [Next record](cancel-the-original-unit-before-supplying-concrete-section-rings.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Evaluate original geometric-stalk units through typed projections

The concrete `germ_nativeStalkIso` proof in
[InverseImage](../../Aglib/AlgebraicGeometry/EtaleCohomology/GeometricPoints/InverseImage.lean)
exhausted the standard 200000-heartbeat budget at `whnf` while rewriting the
skyscraper-unit and product-projection equations. The same failed invocation
also could not expose the native `getLimitCone` coordinate under implicit
transparency. Run `remote-6650b3f43f4d4c8cab861c845d46666e`, source
`02e7d71b78e61458e983cf345c865d595708d95991da2b34f3ebce8c3ae48cf9`,
still supplies successful Skyscraper-provider coverage only.

First evaluate the native point's skyscraper unit through its fully typed
presheaf arrow and constant-product projection, retaining the original
`toPresheafFiber` germ. Then apply the bounded `projection_composite` helper
with all six arrows and both coordinate laws explicit. Its concrete inputs
are the original inverse-image unit, skyscraper unit, right-adjoint
comparison, product projection, pulled-back-point projection, and geometric
germ. This avoids reconstructing the concrete stalk underneath product
projections. The final natural-isomorphism hom is still literally `stalkUnit`.

Run `remote-9f4b9afd86444d30b10df5c6db78f100`, source
`4aa83877118ceed0c631490c01354f8c01c426e2b13a99de184fc48abc6fbe97`,
accepted Projection and InverseImage in 3.213 and 7.254 seconds, reusing the
unchanged Skyscraper output. Total build wall was 15.444 seconds with peak
wrapper RSS 2663747584 bytes. These changed-source observations are not a
matched benchmark and do not isolate one optimizer cause. The canonical
maps, universes, hypotheses and resource budgets remain unchanged.

