# A finite module inside a free module of its generic rank

Import `Aglib.RingTheory.Localization.FiniteRankEmbedding`.
The declarations are in `IsFractionRing`.

Let R be a domain with its specified fraction field F. If M is a finite
R-module and `f : M →ₗ[R] (ι → F)` is injective for finite ι,
`exists_cleared_coordinate_embedding` constructs a nonzero denominator
`c : nonZeroDivisors R` and an injective map

```text
g : M →ₗ[R] (ι → R)
```

such that `algebraMap R F (g x i) = (c : R) • f x i` for every x and i.
The map retains the given coordinates and the original inclusion R→F.

Choose finitely many generators of M and clear their finitely many coordinates
with one common denominator. The preimage of the integral coordinate range is
a submodule containing those generators, so it contains all of M. The inverse
of the coordinate inclusion on its range gives g. Its injectivity follows
from the original injective f and nonvanishing of the same denominator in F.
Freeness of M is not assumed.

For a finite algebra R→S of domains, with specified compatible fraction fields
F and E, `exists_finite_rank_embedding` specializes this construction to give

```text
S →ₗ[R] (Fin (Module.finrank F E) → R)
```

injectively. The field E is finite-dimensional over F by
`IsFractionRing.finite_of_finite_algebra`; a finite F-basis supplies the
coordinates of the original map S→E. Neither normality, separability, locality,
nor a perfect residue field is required.

The completion consumer is
[FiniteSemilocalDegree](../AdicCompletion/FiniteSemilocalDegree.md). It completes
this injection for the whole finite algebra before bounding its individual
completed local factors.
