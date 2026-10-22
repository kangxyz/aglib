# Closed immersions and source stalks

[Noetherian](Noetherian.lean), imported as `Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.Noetherian`, proves that the source of an actual closed immersion is locally Noetherian when the target is, and Noetherian when the target is. The local and global hypotheses are separate statements; no regular-immersion or finite-dimensional assumption is added.

The actual geometric source/property transport supplies the scheme hypotheses used by [coherent closed-immersion direct image](../../Modules/Coherent/Pushforward/ClosedImmersion/README.md). Affine quotient-ring pushforward and coherent exactness are later module-theoretic interfaces.

The Noetherian source lemmas depend directly on native Mathlib Noetherian and closed-immersion theory, below the module-sheaf direct-image construction.

[Spec](Spec.lean), imported as `Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.Spec`, proves `IsClosedImmersion.surjective_of_specMap` for the actual ring map of a closed spectral morphism. No Noetherian, ideal-module or smoothness premise is added.

[ComponentStalk](ComponentStalk.lean) proves
`Scheme.Hom.ker_stalkMap_mem_minimalPrimes_of_irreducibleComponent`.
For a closed immersion from an integral scheme whose image is an irreducible
component, the kernel of its original stalk map is a minimal prime at every
point of the source. The proof uses the canonical spectrum-of-stalk maps and
generic points. Neither Noetherianity nor flatness is required.

## Limits and finitely presented closed superschemes

[Diagrams](Diagrams.lean), imported as
`Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.Diagrams`, constructs native
closed-subscheme cones. In `Scheme.ClosedSubscheme`,
`isLimitIdealCone D f hsup` assumes an actual closed immersion `f : X ⟶ Y`
and an ideal diagram `D : J ⥤ Y.IdealSheafDataᵒᵖ` with
`(⨆ j, (D.obj j).unop) = f.ker`. The cone is limiting in `Over Y`, and every
leg composed with its stage structure map is the original `f`.
The scheme universe is `u`; the object and hom universes of `J` are
independent. Only the forgotten scheme limit `isLimitIdealSchemeCone` adds
`[IsConnected J]`.

[FinitePresentationApproximation](FinitePresentationApproximation.lean),
imported as
`Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.FinitePresentationApproximation`,
defines the corresponding scheme diagram and cone for an actual
`e : X ⟶ Y`, in `Scheme.Hom`. When `e` is a closed immersion and `Y` is qcqs,
`e.finitePresentationApproximationConeIsLimit` proves the limit with original
cone point `X`. Stages are the closed subschemes from finite-type subideals
of `e.ker`. Their structural maps to `Y` are locally finitely presented, and
transitions and cone projections are closed immersions.
`finitePresentationApproximationCone_comp` fixes every triangle:

```lean
e.finitePresentationApproximationCone.π.app J ≫
  e.finitePresentationApproximationStructure.app J = e
```

The [ideal approximation](../../IdealSheaf/README.md) supplies the actual
finite-type subideals. The [over-category adapter](../../Approximation/ClosedSubscheme/FiniteType.lean)
retains point `Over.mk e` and is consumed by the closed-envelope and
[proper approximation](../../Approximation/Proper/README.md) constructions.
These stages are closed superschemes, without a nilpotent-thickening premise
or conclusion.
