# Finite-etale cover towers and coherent algebraization

The cover-tower namespace is `Scheme.FiniteEtale.Adic`; section-algebra and
good-open constructions also extend `Scheme.Modules.Algebra`.

## Affine fullness and local residue comparison
[Affine](Affine.lean) constructs `fibreIso` and `fibreMap` for the literal
tensor-product affine fibre and proves their projection/naturality formulas.
`affine_fibre_hom_lift` lifts an actual morphism of closed affine fibres which
commutes with their base maps. Its assumptions are a Noetherian commutative
ring `R`, an ideal `I`, `IsAdicComplete I R`, an `R`-finite target algebra
`B`, and a formally smooth source algebra `A`. It reuses
`Algebra.FormallySmooth.tensorProduct_map_surjective_of_finite`.

[Fullness](Fullness.lean) gives the full instance
`quotient_baseChange_full` for actual finite-etale covers of `Spec R` under
those Noetherian and adic-completeness assumptions. The coordinate algebra and
its finite/étale properties come from each cover's original structure map.
The statement is fullness; it does not construct a proper-Henselian
finite-etale equivalence.

[Residue](Residue.lean) gives `marked_closed_full` for a Noetherian local ring
complete for its maximal ideal and an actual residue-field marking. Full and
faithful pullback along an actual scheme isomorphism is owned separately by
[BaseChange.Isomorphism](../BaseChange/Isomorphism.lean), with no completeness
or Noetherianity assumption.

[RationalPointCompletion](RationalPointCompletion.lean) specializes the proved
fullness to the completed actual stalk of a rational point on an integral
scheme, assuming that stalk is a DVR. Its residue marking is the constructed
`Scheme.RationalPoint.Completion.residueEquiv`; no residue isomorphism or
completion ring is supplied independently.

The affine fullness interfaces retain the incoming R5 source packet
`f8a3314ddecffcada2ec721d26d56a937bed9690` as provenance. Existing smooth and
completion providers are reused without duplicate declarations.

[Equivalence](Equivalence.lean) combines the existing fullness with locality-only
faithfulness and essential surjectivity from [ResidueLift](../ResidueLift.lean).
For a Noetherian local ring complete for its maximal ideal, it constructs the
actual residue-base-change equivalence, including the exact marked-residue-field
composite and both forward projection formulas. The Noetherian and completeness
hypotheses remain explicit; proper-scheme comparison is a separate theorem.

## Original cover towers

[StageBaseChange](StageBaseChange.lean) proves that base change between
positive ideal-power thickenings is the original nilpotent equivalence.
[CoverSystem](CoverSystem.lean) constructs an actual cover tower from a
specified first-stage finite-etale cover. The zeroth stage is its pullback to
the empty thickening; it is not obtained by applying a positive-stage
nilpotence assertion at zero. [CoverSystemHom](CoverSystemHom.lean) uniquely
lifts a prescribed first-stage map between the original chosen towers.

[CoverSystemModules](CoverSystemModules.lean) takes the actual finite
structure-module direct images, proves coherence under local Noetherianity,
and constructs their native adic system. The original transitions and quotient
units give adicity. [AlgebraStructure](AlgebraStructure.lean) and
[CoverSystemHomModules](CoverSystemHomModules.lean) retain their native
commutative algebra structures and the contravariant stagewise algebra maps.
[StageModuleComparison](StageModuleComparison.lean) fixes the original-unit
certificate for affine base change; [StageAlgebraComparison](StageAlgebraComparison.lean)
and [StageAlgebraEtale](StageAlgebraEtale.lean) identify the actual quotient
section algebras and their etaleness.

For a given global cover, [CompletionComparison](CompletionComparison.lean),
[RestrictionTransitions](RestrictionTransitions.lean), and
[CompletionNaturality](CompletionNaturality.lean) compare its restriction
tower with the original coherent completion, retaining every original
projection and morphism. [GlobalAlgebraData](GlobalAlgebraData.lean) keeps
the global cover's existing algebra structure and all its reduction maps.

## Recovering actual covers and maps

[AlgebraHomReconstruction](AlgebraHomReconstruction.lean), using the actual
[inverse-image affine cover](AlgebraHomAffineCover.lean) and its
[chart maps](AlgebraHomAffineCharts.lean), reconstructs a unique original
scheme map from a unit- and multiplication-preserving map of direct-image
structure modules. It applies to affine structural maps, including finite
maps, without etaleness, properness, Noetherianity, or completeness.
[CompletionFullness](CompletionFullness.lean) therefore obtains
`firstStage_baseChange_full` on a locally Noetherian scheme from full
faithfulness of its specified coherent completion functor. This input lifts
maps and does not assert object effectivity.

[CoherentAlgebraGluing](CoherentAlgebraGluing.lean) keeps the original section
algebras and cartesian restriction squares.
[GoodAffineNeighborhood](GoodAffineNeighborhood.lean) passes from etale
actual target-stalk base change to good affine opens.
[CoherentGoodOpens](CoherentGoodOpens.lean) applies the finite local algebra
criterion to all positive-power reductions. For a locally Noetherian scheme
universally closed over a local ring and a proper base ideal, those good opens
cover the whole scheme. [GoodAffineGluing](GoodAffineGluing.lean) uses native
relative gluing of their section spectra;
[GoodAffineComparison](GoodAffineComparison.lean) retains the original local
comparison maps. No finite subcover or general relative spectrum is required.

Given an original cover tower and `AdicAlgebraizationData` for its coherent
adic system, [AlgebraizedCover](AlgebraizedCover.lean) derives the all-order
etaleness premises from the given stages and constructs the actual finite-etale
cover under those local-base hypotheses.
[AlgebraizedCoverComparison](AlgebraizedCoverComparison.lean) supplies its
specified isomorphism with every original stage, including the first.
[ResidueStage](ResidueStage.lean) identifies that first stage with the literal
residue-field pullback and retains its inclusion into the original scheme.
The [proper complete-local endpoint](../ProperCompleteLocal.md) supplies
coherent algebraization from proper Grothendieck existence over a maximal-ideal
complete Noetherian local base.
