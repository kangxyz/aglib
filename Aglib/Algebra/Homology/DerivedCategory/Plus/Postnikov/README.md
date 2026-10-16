# Finite native homology layers

[Layers](Layers.lean) proves that the original native truncation inclusion
and projection induce isomorphisms on their retained homology degrees.
Their forward maps are exactly homology of those original arrows.
`isoSingleHomology` is the fully faithful bounded-below lift of the
unique normalized comparison in [TStructure/Homology](../../TStructure/Homology.lean).
It retains the original homology and its native single functor.

The [parent Postnikov leaf](../Postnikov.lean) proves
`DerivedCategory.Plus.property_of_homology_bounds`. An isomorphism-stable
property containing zero and closed under native distinguished extensions
holds on a bounded-homology object whenever it holds on the singles of
its original homology in the specified interval. Empty intervals are
included. No upper term bound, coherent representative, enough injectives
or target geometric hypothesis is a premise.

Proper coherent-image and smaller-support cone arguments consume this
one induction. Natural-transformation comparisons and fixed-degree D+
truncation use the same layers; geometry does not introduce another
homology-layer induction or replacement cohomology object.

[Comparison](Comparison.lean) upgrades a shift-compatible comparison of
triangulated functors to all bounded-below objects when both functors preserve
the native lower bounds. The objectwise version needs invertibility only on
singles of that object's original homology; the functorial version needs it on
all native singles. Each fixed homology degree uses one finite upper truncation
and the original truncation inclusion. There is no upper term bound,
cohomological-dimension assumption or convergence premise. The parent leaf's
`isIso_app_of_homology_bounds` is the common finite-interval argument.
