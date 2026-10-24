# Original derived compactification comparisons

`Comparison` constructs the actual bounded-below module refinement map from
its original derived adjunction unit and genuine Cartesian open pullback
comparison. All source, ambient and derived-category universe parameters are
retained. It does not assume or prove that the map is invertible merely
because a common refinement exists.

`PullbackCoherence` derives the identity and composition equations for the
original Cartesian open comparison using the installed inverse-image
comparisons. `Coherence` proves `moduleDerivedRefinementComparison_id` and
`moduleDerivedRefinementComparison_comp` for the unchanged refinement map.
Their equations use the original derived direct-image identity and composition
isomorphisms, the actual adjunction units, and the original Cartesian open
comparisons. All source and ambient derived-category universes remain
independent. No proper-base-change or invertibility premise is used.

Proper-base-change invertibility for torsion cohomology and choice-independent
exceptional images remain separate consumers. These coherence equations do
not make the refinement transformation invertible. Compilation evidence is
tracked for exact source versions.
