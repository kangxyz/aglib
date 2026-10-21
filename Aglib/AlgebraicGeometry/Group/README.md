# Actual group-scheme pullback

[ScalarExtension](ScalarExtension.lean), imported as `Aglib.AlgebraicGeometry.Group.ScalarExtension`, owns `AlgebraicGeometry.Scheme.Group.BaseChange`. `GroupSchemeBaseChange f` packages an actual functor on group objects with an explicit underlying comparison to scheme pullback.

The canonical `groupSchemeBaseChange f` is `Over.pullback f` lifted by `mapGrp`. `groupSchemeBaseChangeId` and `groupSchemeBaseChangeComp` give natural identity/composition isomorphisms for that canonical constructor. `pullbackFiberMulEquiv` compares actual multiplicative point fibres, including projection and naturality formulas. These are natural comparisons of chosen pullbacks, not strict equality of choices or coherence asserted for every arbitrarily supplied functor.

`GroupSchemeScalarExtension` specializes the same interface along the contravariant spectrum map of a field homomorphism. Mathlib group objects and cartesian monoidal over-categories are the lower prerequisites. Original group/isogeny applications remain external; no local-field embedding, isogeny-extension or discriminant criterion is supplied.

[PointedMorphism](PointedMorphism.lean), in `Scheme.Group.PointedMorphism`, proves product rigidity and
that an identity-preserving actual morphism of proper group schemes over a
field is a group homomorphism when the source is geometrically integral. The
algebraically closed intermediate result requires the actual tensor square
of the source to be integral. The target has no smoothness, connectedness or
curve assumption. `Geometrically.Integral.SmoothCurve` supplies the separate
smooth connected curve implication; no conditional `GeometryBackground`
parameter is silently filled by the mere existence of the group theorem.

MultiplicativeGroup constructs the actual Laurent-affine multiplicative group
and its relative group object, with power kernels representing the existing
roots-of-unity functor. RootsFiniteEtale proves finiteness at positive levels
and etaleness only with an invertible level. MultiplicativeBaseChange proves
actual base-change isomorphisms, coordinates and identity/composition formulas.
RootCover constructs actual root schemes and their torsor action. RootsHopfAlgebra
constructs the quotient Hopf algebra and its actual root-valued geometric points;
PrimitiveRootCover supplies the finite free cyclotomic cover, etaleness with an
invertible level, primitive field points, and level one. [BaseChange/PointTransport](BaseChange/PointTransport.lean) gives the
ordinary point and group-map composition identities with the specified closure
embeddings and original finite/etale conditions.

Focused interface guides: [Comparisons of given etale group quotients](EtaleQuotient.md).

[Characteristic-zero curve isogenies](../Curves/Isogeny/Etale.md) prove
etaleness of the actual finite surjective homomorphism between smooth proper
geometrically connected curve group objects. The native
`Curve.charZeroFiniteCurveGroupHomEtale` supplier discharges the retained
input of `Curve.pointed_dominant_finite_etale`; the direct proved adapter keeps
the original curve map and origin equation.

[Point/divisor compatibility](PointDivisor.md) identifies the actual normalized degree-zero
Abel class with the supplied group multiplication and power maps on every test
scheme, under the native curve and coherent-genus-one hypotheses. The producer
uses the native geometric and Cartier suppliers without a representing witness
or `hrep` input.

[Multiplication degree](MultiplicationDegree.md) proves that the literal `[n]`
is finite étale with geometric degree `n²` and native locally free rank `n²`,
under the explicit `hG : Curve.Properties G.X`, `hg1 : coherentGenus k G.X = 1`
and `IsUnit (n : k)` hypotheses. An external genus field still requires its
separate identification with the native coherent genus.
