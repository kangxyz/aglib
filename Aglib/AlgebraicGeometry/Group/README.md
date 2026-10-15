# Actual group-scheme pullback

[ScalarExtension](ScalarExtension.lean), imported as `Aglib.AlgebraicGeometry.Group.ScalarExtension`, owns `AlgebraicGeometry.Scheme.Group.BaseChange`. `GroupSchemeBaseChange f` packages an actual functor on group objects with an explicit underlying comparison to scheme pullback.

The canonical `groupSchemeBaseChange f` is `Over.pullback f` lifted by `mapGrp`. `groupSchemeBaseChangeId` and `groupSchemeBaseChangeComp` give natural identity/composition isomorphisms for that canonical constructor. `pullbackFiberMulEquiv` compares actual multiplicative point fibres, including projection and naturality formulas. These are natural comparisons of chosen pullbacks, not strict equality of choices or coherence asserted for every arbitrarily supplied functor.

`GroupSchemeScalarExtension` specializes the same interface along the contravariant spectrum map of a field homomorphism. Mathlib group objects and cartesian monoidal over-categories are the lower prerequisites. Original group/isogeny applications remain external; no local-field embedding, isogeny-extension or discriminant criterion is supplied.
