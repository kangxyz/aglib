# Shift-compatible original derived composition units

[Shift](Shift.lean) proves `rightDerivedFunctorPlusCompUnit_commShift`
for the original comparison unit in [the parent composition leaf](../Composition.lean).
It uses the native termwise-functor comparison, associators and installed
derived units, retaining all category/morphism/derived-model universes.
Neither functor needs to preserve homology or injectives for this shift
compatibility. The source categories retain enough injectives to define
the installed right-derived functors. Original geometric base-change
comparisons consume this same unit.

[SingleUnit](SingleUnit.lean) proves composition and functor-isomorphism
coherence for the installed `rightDerivedSingleUnit`. For additive
functors between abelian categories with the stated enough-injective and
selected-derived-category structures, its equation retains the original
derived comparison and coefficient single unit. It does not assume that
comparison invertible. Category, morphism and derived-model universes remain
separate.
