# Localization into the native bounded-above derived category

[Localization](Localization.lean) is imported as
`Aglib.Algebra.Homology.DerivedCategory.Minus.Localization`. It uses Mathlib's
actual `DerivedCategory.Minus C`, the bounded-above full subcategory of the
ambient derived category. The ambient abelian category and its object,
morphism and chosen derived-category universes remain explicit.

`CochainComplex.truncationToBounded` is the actual good upper truncation.
Its counit is the original truncation chain map; truncation preserves original
quasi-isomorphisms. For every pair of genuinely term-bounded complexes, some
common truncation degree makes both counits quasi-isomorphisms. The generic
[approximation criterion](../../../../CategoryTheory/Localization/README.md)
therefore proves full faithfulness of the localized inclusion. Actual bounded
representatives prove essential surjectivity.

`boundedAboveDerivedEquivalence` and `boundedAboveQMinus_isLocalization` retain
the resulting equivalence and localization structure on the canonical functor
from [bounded-above complexes](../../CochainComplex/BoundedAbove/README.md).
The factorization isomorphisms retain the original ambient `DerivedCategory.Q`.
Enough projectives or injectives are not hypotheses of this localization result;
no alternative ambient derived category or global standard instance is defined.
