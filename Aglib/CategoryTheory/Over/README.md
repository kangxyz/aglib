# Pullback maps and fixed fibres

[FixedFiberHom](FixedFiberHom.lean) constructs the actual fixed-fibre Hom equivalence of a specified Cartesian square. Its chosen-pullback specialization retains the original forward projection and inverse lift. Isomorphism and base-equality transport, Over precomposition, and the split-base lift keep their original maps and universal-property equations. The category and Hom worlds remain independent, with no scheme or field premise in the general constructions.

[PullbackMaps](PullbackMaps.lean) constructs right-cospan maps in the original standard and flipped pullback orders, proves their projection and composition laws, and identifies the actual fibre map with the pasted Cartesian comparison. Only invertibility requires the original IsPullback premise.

The étale fixed-point comparison adapters and the common-point geometric-fibre base-change map use these same constructors and projections.
