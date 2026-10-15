# Stupid truncation maps and exact layer sequences

[Maps](Maps.lean), imported as `Aglib.Algebra.Homology.Embedding.StupidTrunc.Maps`, gives `CochainComplex.stupidTruncGE`, its actual inclusion/naturality and degreewise splitting. `HomologicalComplex.stupidTruncXIso_hom_d` compares the original differential under an actual relation-reflecting embedding.

[Transition](Transition.lean) gives `stupidTruncGETransition` with the original inclusion, identity and composition formulas. [Layer](Layer.lean) constructs `stupidTruncGELayerSequence` and its short exactness and splitting properties. Objects are actual integer-indexed cochain complexes in an abelian category. No lower/upper boundedness or projectivity premise is assumed by this ordinary-complex layer construction.

The split property is termwise, through [degreewiseSplitMono](../../CochainComplex/DegreewiseSplitMono.lean), and need not be a chain retraction. [Bounded homotopy comparison](../../HomotopyCategory/Plus/README.md) and [D+ term comparison](../../DerivedCategory/Plus/README.md) consume the actual layer sequence and single-object maps.
