# Section spans and original total-unit equations

[Span](Span.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.Godement.Section.Span`, uses actual section/projection maps with the specified composite identity. It constructs `Scheme.Modules.Godement.sectionComplexPlusIso`, total-image objects and the bounded-below map from one total to the repeated resolved construction.

[Units](Units.lean) identifies the original pushed-unit and derived-unit maps in that span. [Localization](Localization.lean) expresses the corresponding comparisons after the native D+ localization. The original section identity, Plus membership, unit normalization and stated quasi-isomorphism conditions remain attached to the maps.

Consumers are canonical section/direct-image comparison and the actual bounded contraction calculations. A section/projection identity supplies the stated one-sided comparison; it does not assert an inverse section or a two-sided equivalence of scheme categories.
