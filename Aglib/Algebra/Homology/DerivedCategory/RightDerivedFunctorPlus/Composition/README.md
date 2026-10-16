# Shift-compatible original derived composition units

[Shift](Shift.lean) proves `rightDerivedFunctorPlusCompUnit_commShift`
for the original comparison unit in [the parent composition leaf](../Composition.lean).
It uses the native termwise-functor comparison, associators and installed
derived units, retaining all category/morphism/derived-model universes.
Neither functor needs to preserve homology or injectives for this shift
compatibility. The source categories retain enough injectives to define
the installed right-derived functors. Original geometric base-change
comparisons consume this same unit.
