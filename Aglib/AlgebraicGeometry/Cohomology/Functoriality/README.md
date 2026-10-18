# Actual pullback on cohomology

[Pullback](Pullback.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback`, constructs `AlgebraicGeometry.Scheme.Cohomology.zariskiCohomologyMap` using exact inverse image and an actual coefficient map. It proves coefficient naturality on the original additive `Sheaf.H`.

`zariskiCohomologyMap_map` states this naturality for any commuting
coefficient square; `zariskiCohomologyMap_naturality` is its endomorphism
case.

`structureCohomologyPullbackLinear` is linear for a morphism over the structural field. `structureCohomologyPullbackSemilinear` retains the actual compatible field-change square and gives the corresponding semilinear map. Constant-section and scalar compatibility identify the field action; no new general theorem-family premise is used.

[Isomorphism](Isomorphism.lean) gives bijectivity for an actual scheme isomorphism and the native `structureCohomologyIso`. The maps are the original cohomology pullback maps, with H0 normalization supplied by the coefficient/H0 and base-change comparisons.

The consumers are canonical field base change, affine direct-image comparison and differential-sheaf pullback. [Coefficients/scalars](../Modules/README.md) and native exact inverse image are lower prerequisites.

[DegreeZero](DegreeZero.lean) owns `zariskiCohomologyMap_addEquiv₀` and
`zariskiCohomologyMap_equiv₀`, the original degree-zero normalization independent
of field or base-change assumptions. The former field owner publicly imports
this single implementation.

[Modules](Modules.lean) constructs `moduleCohomologyMapAlong` from an actual
module-sheaf coefficient arrow `M ⟶ f_* N`. The map is the original additive
`zariskiCohomologyMap` applied to its adjoint coefficient map.
`moduleCohomologyMapAlongLinear` is linear for every specified structural ring,
and `moduleCohomologyMapAlong_equiv₀` identifies the actual section map.
`moduleCohomologyPullback` specializes the coefficient arrow to the original
module adjunction unit. Construction uses no quasicoherence, flatness,
properness or finite-generation premise.

[Modules/Composition](Modules/Composition.lean) proves the original additive
coefficient mate's Hom-adjunction formula, coefficient pre/postcomposition,
composition through the native inverse-image comparison, and transport
along equal scheme morphisms with the actual direct-image comparison. These
equations preserve the specified module arrows and have no geometric
flatness or quasicoherence premise. Consequently `moduleCohomologyPullback_map`:
geometric module pullback on cohomology is natural in the coefficient module.

[Pushforward](Pushforward.lean) defines the original `Scheme.Modules.derivedPushforwardPlus` and its unit. [PushforwardComposition](PushforwardComposition.lean) gives the actual D+ composition isomorphism for scheme morphisms and its original unit equation; [PushforwardSection](PushforwardSection.lean) gives the one-sided comparison for a supplied section/projection composite identity.

[PullbackSingle](PullbackSingle.lean), [SingleComparison](SingleComparison.lean), [Contraction](../../Modules/Complex/Contraction.lean) and [PlusQuasiIso](../../Modules/Complex/PlusQuasiIso.lean) retain actual single objects, lower bounds, original units and supplied quasi-isomorphism/contraction data. Flat derived pullback and bounded comparison conditions are separate from ordinary structural pullback. No natural replacement/model choice is inferred.

[PullbackPushforward](PullbackPushforward.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.Functoriality.PullbackPushforward`, constructs `Scheme.Modules.Plus.pullbackPushforwardUnit` on actual bounded-below complexes for an arbitrary scheme morphism. This unit goes from the identity to termwise pullback followed by termwise direct image. Its derived composite `Scheme.Modules.derivedPullbackPushforwardPlus`, `derivedPullbackPushforwardPlusUnitOnPlus` and `derivedPullbackPushforwardPlusUnit` retain flatness and the canonical derived-category choices. The derived composite is `derivedFlatPullbackPlus p ⋙ derivedPushforwardPlus p`; the component equation records the installed derived unit. Ordinary definition and derived comparison have separate hypotheses.

[Identity](Identity.lean) gives `Scheme.Modules.derivedFlatPullbackPlusIdIso` from the actual module pullback identity and the native right-derived identity comparison. [Restriction](Restriction.lean) constructs `Scheme.Modules.derivedRestrictionPlus` for an actual open immersion. `isIso_derivedRestrictionPlusUnit` makes its original right-derived unit invertible, using preservation of homology by the actual exact restriction functor. These interfaces act on the actual D+ module category and require no perfect-object predicate.

[Pushforward/Shift](Pushforward/Shift.lean) exposes the original installed
derived pushforward's native shifts, triangulated structure and unit
compatibility, without a new derived model or geometric hypothesis.

[Modules/Isomorphism](Modules/Isomorphism.lean) proves bijectivity of the
original `moduleCohomologyMapAlong` for a scheme isomorphism and an actual
invertible coefficient arrow, including the original module-pullback unit.
`moduleCohomologyRestrictionIsoOfPullbackIso` retains compatible structural
scalars and an actual ordinary pullback-coefficient isomorphism; its forward
arrow is the same original geometric map. No quasicoherence, Noetherianity
or finiteness is assumed. The [point-fibre coordinate comparison](../Fibers/Affine.lean)
uses this interface. Over a field `k`, `finrank_moduleCohomology_eq_of_isIso`
transports cohomology dimensions along a scheme isomorphism over `Spec k` and a
coefficient isomorphism `e^* M ≅ N`; the fibre Hilbert polynomials of projective
space consume it.
