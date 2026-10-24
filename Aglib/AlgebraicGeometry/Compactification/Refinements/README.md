# Dense compactifications and refinements

`Category.lean` defines `Scheme.Hom.DenseCompactification f` by extending the
existing `Scheme.Hom.Compactification f` with schematic density of its original
open immersion. Its `Refinement` morphisms are actual proper maps preserving
the open and base triangles. Identity, composition, and the faithful functor
`forgetToOver` retain the original scheme morphisms. This category needs no
qcqs or finite-type premise merely to be defined.

`Uniqueness.lean` proves that parallel refinements are equal, using the existing
`Scheme.QuasiDomination.hom_ext_of_schemeTheoreticallyDominant` theorem from
`RationalMap/QuasiDomination/Basic.lean`. That read-only supplier has no
compactification dependency and needs neither reducedness nor quasi-compactness
of the dense map. Schematic density, not topological density alone, is essential
for this uniqueness statement on nonreduced schemes.

For quasi-compact `f`, `Common.lean` constructs `common C D` as the native
schematic image of the original pair into `pullback C.p D.p`. Its actual proper
projections are `commonToLeft` and `commonToRight`; their maps and both triangles
are retained. These constructions give `IsCofilteredOrEmpty`. The separate
`Cofiltered.lean` consumes the supplied Nagata theorem under a qcqs target and
separated finite-type `f` to prove nonemptiness and `IsCofiltered`.

`OpenSquare.lean` proves `isPullback_open` for any refinement of compactifications
of a quasi-compact `f`. Its `openLift` to the literal pullback is an open
immersion, a proper section, and dominant, hence an isomorphism. Its projection
equations are `openLift_fst` and `openLift_snd`. This is scheme geometry, with no
sheaf-theoretic proper-base-change premise.

Common refinements and Cartesian open squares are proved results, not fields
assumed by the category. Arbitrary base change is not claimed to preserve
schematic density. Nagata existence remains owned by `Compactification/QCQS.lean`;
no existing generic or Nagata source is rewritten here.

`Densification.lean` normalizes any compactification with quasi-compact open
source by its native scheme-theoretic image. `densifyι` is the original closed
image inclusion; `isPullback_densify` identifies its original open square.
`densifyMap` and `densifyRefinement` lift compatible ambient maps by the existing
closed-target factorization theorem and retain the original inclusion equations.

`BaseChange.lean` defines the actual normalized `DenseCompactification.baseChange`
functor for quasi-compact `f` and any new-base morphism `b`. It first consumes
`Compactification.baseChange` and then densifies. `baseChangeNormalization`
is a closed comparison to the unnormalized ambient pullback, and
`baseChange_map_normalization` identifies every normalized map with the original
ambient pullback map after that inclusion. Projection equations and the Cartesian
normalization square are retained. No assertion that schematic image commutes
with arbitrary base change is made. The original coherence comparisons are
described below.

`OpenRestriction.lean` restricts a dense compactification over a quasi-compact
open target. The intermediate scheme and its proper structural map are literal
pullbacks; source density uses the existing schematic-density open-factor
theorem with its explicit quasi-compactness premise.

`Composition.lean` packages two actual compactifications as
`Scheme.Hom.CompactifiedComposition f g`. It supplies the proper composite
compactification, the intermediate compactification of `f`, its open map to the
source ambient scheme, and the actual Cartesian proper/open square. Supplied
Nagata gives nonemptiness for separated finite-type `f` and `g` over a qcqs
final base. This geometry does not assert a cohomological compactification
comparison or exceptional-direct-image functor.

`CompositionRefinement.lean` constructs a compatible common tower from the
actual common compactifications of the middle scheme and the composite source.
The structural map lifts through the former's closed image by schematic density;
properness follows by cancellation against its proper map to the final base.
Both actual tower projections and their commutative structural squares are
retained. The construction requires quasi-compactness of the two original maps,
not a further existence hypothesis or a supplied common-refinement field.

`CompositionRestriction.lean` induces the actual proper refinement of the
intermediate compactifications from a compatible tower refinement. Its map is
the literal pullback lift, with equations preserving the original open maps and
proper projections. This restriction requires only quasi-compactness of the
second original map. Derived comparison coherence remains a separate
mathematical obligation.

## Original source transport and normalized base-change coherence

`SourceIso.lean` extends the supplied `Compactification.ofSourceIso` to dense
compactifications and refinement functors without changing ambient maps.
`ClosedAmbient.lean` constructs actual proper comparison maps between dense
compactifications embedded into the same ambient, by the existing closed-target
lifting theorem. When both embeddings are closed, the two comparisons form an
isomorphism; their original inclusion equations are retained.

`BaseChangeIdentity.lean` uses the native identity-pullback second projection as
the source isomorphism. Its natural comparison has underlying ambient map equal
to the original normalization followed by that original second projection.

`BaseChangeIterationAmbient.lean` base-changes the first normalization inclusion,
composes the second normalization, and uses the native
`pullbackRightPullbackFstIso` on the raw ambient. It supplies an actual closed
immersion into the single raw pullback with original source and projection
equations. `BaseChangeIteration.lean` compares this dense closed ambient with
the single normalization, after the native source transport, and proves
naturality and the original inclusion equation. This requires quasi-compact
`f` but no flatness or qcqs condition on either new base.

`BaseChangeAssociator.lean` identifies the two actual native triple pullback
associators from their original projections, including `pullback.congrHom` for
base-map associativity. It applies to both original sources and raw ambients.
`SourceIsoCoherence.lean` supplies identity-ambient comparisons for composed
source transports, and `SourceIsoEquality.lean` retains identity ambient maps
when equal source isomorphisms are identified.

`BaseChangeSourceIso.lean` compares normalized base change and actual source
transport in the same raw ambient, with the original pullback source map and
inclusion equation. Its interface explicitly assumes quasi-compactness of both
source maps related by the given isomorphism. `BaseChangeCongr.lean` retains the
original source and ambient `pullback.congrHom` identifications for an equality
of base maps.

`BaseChangeTriple.lean` assembles the two actual pasted normalized comparisons
from those interfaces. The source endpoints are first identified by the native
triple associator theorem; only then is thinness applied. It records naturality,
equality after the original final normalization inclusion, and its structural
projection. This geometric coherence is not a derived exchange or
exceptional-direct-image coherence theorem.
