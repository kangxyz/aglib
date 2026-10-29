# D+ triangles, bounded comparison and one-sided contraction

[ShortExact](ShortExact.lean), imported as `Aglib.Algebra.Homology.DerivedCategory.Plus.ShortExact`, gives `DerivedCategory.Plus.triangleOfSESPlus`, `triangleOfSESPlus_distinguished` and `triangleOfSESPlusMap`. The coefficient category is abelian with `HasDerivedCategory`; the supplied short complex of bounded-below complexes has an actual short-exact underlying ordinary complex. The triangle and its functorial arrows use that sequence, without a chosen injective resolution.

[SingleTriangle](SingleTriangle.lean) and [SingleTriangleNaturality](SingleTriangleNaturality.lean) specialize to actual single objects and their original triangle maps. [BoundedComparison](BoundedComparison.lean) gives `DerivedCategory.Plus.isIso_app_of_term_bounds`: an already defined shift-compatible triangulated comparison is propagated from degree-zero single objects under actual lower and upper zero-term bounds. The comparison is not an unbounded-above theorem or a natural model-choice result.

[ExactDerivedContraction](ExactDerivedContraction.lean) gives `DerivedCategory.Plus.exactDerivedContractionIso` and its unit equation. It assumes an abelian category with enough injectives and a derived category, additive endofunctors `F,G`, `G.PreservesHomology`, and an actual `F ⋙ G ≅ Id`. The conclusion is the one-sided `RF ⋙ RG ≅ Id` with the installed unit compatibility. No opposite-composition isomorphism or two-sided equivalence is supplied.

The lower subjects are [distinguished-triangle comparison](../../../../CategoryTheory/Triangulated/README.md), [actual truncation layers](../../Embedding/StupidTrunc/README.md) and [right-derived unit comparisons](../RightDerivedFunctorPlus/README.md). Godement contraction and original scheme D+ comparison are the current consumers. Source correspondence is recorded in [latest-homology](../../../../../docs/migration/latest-homology.json).

[Postnikov](Postnikov/README.md) gives the complementary cohomological
interface: native truncation homology, normalized single layers, and one
finite extension induction under homology bounds. The terms of the
chosen object need not be bounded or satisfy the property. Proper
coherent images and flat-base-change comparisons share this lower tier.

[InjectiveComparison](InjectiveComparison.lean) extends actual shift-compatible
triangulated comparisons from injective singles to every single by finite
homology-degree induction.
[InjectiveComparisonExact](InjectiveComparisonExact.lean) performs the complete
assembly after an exact coefficient functor: it derives that functor internally,
proves the two native lower bounds, and transports the same comparison through
the native exact-single isomorphism. Injectivity is required only in the genuine
coefficient category. The coefficient-derived model stays inside the proof; the
four value-category models and their universes remain independent.

[Ext](Ext.lean) identifies each original Ext group with shifted Hom between
native bounded-below singles, additively and with independent Ext and derived
size universes. The forward lift uses the fully faithful inclusion and its
original shift comparison. It preserves Yoneda composition, degree-zero maps
and the actual unsigned `singleTrianglePlus` connecting arrow. No
injective or projective availability hypothesis is added. A protected signed
`Ext.δ` must retain its original sign when used by a derived comparison.
