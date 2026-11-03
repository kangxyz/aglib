# Conditional original point-blowup canonical frame

Source: [PointBlowupFrame.lean](PointBlowupFrame.lean).

Import:
`Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.PointBlowupFrame`.

## Exact original map

Let `b : Z → P` be the actual point blowdown, `S = P.presheaf.stalk x`,
`s : Spec S → P`, `p : B → Spec S` the actual maximal-ideal blowup, and
`a : B → Z` its original `stalkBlowupComparison`. Write `ωP` and `ωZ` for
the canonical modules selected by the supplied original global projective
embeddings over `R`.

`normalSurfaceCanonicalLocalSpectrumIsoOfSelfInjectiveDimension` constructs
`eS : s*ωP ≅ O_(Spec S)` from finite native self-injective dimension of
**this original parent stalk**. It is the inverse of the existing
`canonicalLocalSpectrumCoefficientIso`, followed by tilde of the existing
`normalSurfaceCanonicalStalkLinearEquivOfSelfInjectiveDimension` and the
native `tildeSelf`. It constructs no canonical module on an arbitrary local
model and uses no finite `R → S` premise.

`normalSurfacePointBlowupFramedCanonicalPullback` is the literal composite

```
λ = (pullbackUnitIso p).inv
    ≫ (pullback p).map eS.inv
    ≫ (ordinaryTracePullbackSquareIso a p b s H).inv.app ωP
    ≫ (pullback a).map (ordinaryTracePullback b τ),
```

where `H` is the original square and `τ` the original proper canonical
trace. The actual derived structure unit and trace isomorphisms are proved
from original rational point-blowup geometry, not added as caller premises.

## Conditional conclusion

The `..._epi_of_exceptional_generation` theorem applies the accepted
`Trace/PointBlowupGeneration` conclusion to this same map after its three
invertible prefixes. Its generation premise is **exactly**
`Epi (globalSectionsEval (i*(a*ωZ)))`, with `i : E → B` the full exceptional
closed immersion. It is not generation on the reduced exceptional scheme.

`localizedCanonical_mem_support` uses the existing full support of `ωZ`
at the actual image point, `localizedCanonical_stalkMap_isIso`, the native
scalar-extension adjunction unit, and `pullbackModuleStalkIso`. It neither
introduces a new generic frame nor needs to prove that `a` preserves generic
points. The `..._isIso_of_exceptional_generation` theorem then applies
`isIso_unitHom_of_epi_of_generic_mem_support` to **the same** `λ`.

`normalSurfacePointBlowupCanonicalIsoOfExceptionalGeneration` returns
`a*ωZ ≅ O_B` as `(asIso λ).symm`, not as an independently chosen local frame.

## Boundary and consumers

The isomorphism theorem retains the exact original global-model,
projective-embedding, dimension, normality, Nagata, rationality and residue
triangle telescope of `Trace/PointBlowupGeneration`. The only new
mathematical premise is a native bound
`[HasInjectiveDimensionLE (ModuleCat.of S S) d]` at the original parent.
No later completeness, finite later stalk, successor frame, inverse-line
identification, Hilbert function or cone is assumed.

The full exceptional-generation premise remains explicit.
A separate inverse-line consumer can
restrict this same frame and cancel the actual positive exceptional line
in `localizedExceptionalCanonicalRestrictionIso`, retaining the same
projective embedding and original derived residue coefficient line.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/Trace/PointBlowupInverseLine](PointBlowupInverseLine.md).
