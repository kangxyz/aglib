# Computing the original D+ direct image

[Total](Total.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.Godement.DerivedPushforward.Total`, gives `Scheme.Modules.Godement.godementTotalDerivedPushforwardIso`. On actual bounded-below complexes, pushforward of the canonical Godement total, followed by the native D+ localization, agrees with the original `derivedPushforwardPlus`.

The augmentation/unit equations use the installed derived unit, not an independently chosen comparison. [Sheaf](Sheaf.lean) specializes the construction to actual single module sheaves and their original Godement resolution.

The lower [bounded augmentation](../TotalComplex/README.md) and [termwise/local flasque unit calculation](../../Flasque/README.md) supply the proof route. Projection formula, section comparisons and base-change unit normalization consume this same D+ isomorphism. This is not an unbounded-derived calculation or a classical proper-finiteness theorem.
