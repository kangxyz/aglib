# Finite-etale closed-fibre fullness over an adically complete base

The native namespace is `Scheme.FiniteEtale.Adic`.
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

The incoming source is the hash-pinned R5 packet at
`f8a3314ddecffcada2ec721d26d56a937bed9690`. Existing smooth and completion
providers are reused without duplicate declarations.
