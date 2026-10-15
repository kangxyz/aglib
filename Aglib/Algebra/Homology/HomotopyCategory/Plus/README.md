# Comparison from single terms with two term bounds

[BoundedComparison](BoundedComparison.lean), imported as `Aglib.Algebra.Homology.HomotopyCategory.Plus.BoundedComparison`, gives `CochainComplex.isIso_app_of_term_bounds`. The comparison is already defined between shift-compatible triangulated functors on the actual bounded-below homotopy category. A complex with actual upper and lower zero-term bounds inherits componentwise invertibility from the corresponding original single terms.

`brutalPlus` and `singlePlus` retain the actual complex/truncation objects. The source shift convention is `CategoryTheory.shiftFunctor`; the distinguished-triangle step preserves its original compatibility. The result is not an unbounded-above comparison or a functorial choice of a projective/injective model.

Lower [layer sequences](../../Embedding/StupidTrunc/README.md) and [middle-isomorphism detection](../../../../CategoryTheory/Triangulated/README.md) supply the argument. The analogous actual [D+ comparison](../../DerivedCategory/Plus/README.md) is a separate interface.
