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

[Multiplication torsion](MultiplicationTorsion.md) constructs a
`Module.Basis (Fin 2) (ZMod n)` on the literal
`MultiplicationKernel.finiteTorsionPoints E n` of a commutative curve group.
It retains `hE : Curve.Properties E.X`, the native
`hg1 : coherentGenus F E.X = 1`, `0 < n` and `IsUnit (n : F)`.
Its canonical scalar action, linear Galois action and semilinear actual level
maps keep the original carrier and underlying functions. The chosen basis is
not asserted Galois-equivariant. Level one is covered.
[Weil pairing](WeilPairing.md) supplies an actual perfect alternating pairing
at positive invertible levels, including one, even and composite levels, with
the original torsion and roots-of-unity Galois actions.

[Native curve genus](CurveGenus.md) proves `Curve.coherentGenus k G.X = 1`
from the actual group object and `Curve.Properties G.X` over every field,
including characteristic two. It does not identify an external genus field.
[Positive-level multiplication](MultiplicationFiniteDegree.lean) proves that
the actual `[n]` is finite, flat and surjective of locally free rank `n²` for
every positive `n`, including noninvertible levels, with the native genus-one
premise supplied by the genus theorem. The geometric reduced point-count and
étaleness conclusions above retain their invertible-level premise.

[Multiplication by `n` with finite `k`-point fibres](MultiplicationSurjective.lean):
for a group scheme `G` over an algebraically closed field `k`, proper over `k`,
and `n` such that `{p | p ^ n = y}` is finite for every `k`-point `y`, the
literal `[n] = (𝟙 G) ^ n` is finite
(`multiplication_isFinite_of_finite_setOf_pow_eq_of_isAlgClosed`); if `G` is
moreover connected, `[n]` is surjective
(`multiplication_surjective_of_finite_setOf_pow_eq_of_isAlgClosed`) and `G(k)` is
`n`-divisible (`exists_pow_eq_of_finite_setOf_pow_eq_of_isAlgClosed`). For an
abelian variety these are Stacks 03RP (3), (4) and the finiteness in the proof
of 0BFG; here the finiteness of the `k`-point fibres is the hypothesis, and no
smoothness, commutativity, ample line bundle or dimension bound is used.
`multiplication_left_apply_point`, `multiplication_left_apply_unitPoint` and
`multiplication_isProper` hold over any field. Consumer: the Jacobian
([Curves/Jacobian/Multiplication](../Curves/Jacobian/Multiplication.lean)).

[IdentityComponent](IdentityComponent/README.md): the identity component of a group scheme locally
of finite type over a field: open, closed, geometrically connected, a group scheme, compatible with
field extension, geometrically irreducible, quasi-compact and of finite type.

[IsogenyPairing](IsogenyPairing.lean) obtains frame-evaluation characters from the
same positive transporter and framed character in
[generic sheaf-torsor transport](../../CategoryTheory/Sites/Torsor/Transport.lean).
The original coefficient-unit fixedness supplies the character hypothesis;
`scalar_eq_framedScalar` and `character_eq_framedCharacter` identify the actual
units-valued maps. Frame and equivariant-isomorphism independence retain the
original deck action and positive sign.
