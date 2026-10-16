# Topological sheaves and dimension

[Sheaves](Sheaves/README.md) works on actual topological sheaves, stalks and opens. Main results are basis detection of exactness/acyclicity, actual Mayer–Vietoris sequences, Noetherian-space filtered-colimit sheafification and closed-support comparison without Noetherianity.

[KrullDimension](KrullDimension/README.md) proves that a closed subset avoiding all component generic points lowers a finite topological dimension bound in a quasi-sober space. Its separate disjoint-neighborhood auxiliary lemma retains Noetherianity.

These subjects precede scheme-specialized module and cohomological-dimension arguments. Native declaration owners include `TopCat.Sheaf` and `TopologicalSpace`; source imports use `Aglib.Topology`.

[Semicontinuity](Semicontinuity.lean) proves that two upper semicontinuous
natural-valued functions with locally constant sum are individually locally
constant. It is the pure numerical input for the reduced local Grauert
criterion on original module-complex homology.
