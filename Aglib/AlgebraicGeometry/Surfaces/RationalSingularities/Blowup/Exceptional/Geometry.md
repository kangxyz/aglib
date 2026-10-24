# Geometry of the original exceptional curve

The input is a commutative Noetherian Nagata normal local domain A of dimension
two satisfying the genuine `NormalModificationH1Vanishing A` predicate. X is
the original ordinary maximal-ideal blowup. E is its full exceptional scheme,
with the original inclusion i and the original residue structure map
E→Spec(A/m). Nilpotents in E are retained. Regular and singular A are allowed.

`exceptionalTautologicalEmbedding` restricts the actual ordinary finite-row
embedding through the native projective-space coefficient base-change square.
It retains both original triangles: its composition with the projective
coefficient map is i followed by the ordinary embedding, and its structural
map is the original exceptional structure map. Closedness follows from the
original closed immersion and the separated coefficient morphism.

`exceptionalTautologicalEmbeddingTwistingIso` is the composite of the native
coefficient twisting-sheaf pullback, the actual two composition comparisons,
and the original ordinary positive-twist comparison. Its target is exactly
`exceptionalLine`, the original i*I for I=m O_X. The finite-generator existence
theorem pads the original row by two zero entries and therefore supplies an
ambient projective dimension at least one without changing its span.

`exceptionalPowerOneCotangentEquiv` identifies the existing native first power
layer with the actual cotangent space m/m² over the original residue field.
The Noetherian local generator inequality gives dimension at least two.
The original degree-zero coefficient isomorphism excludes nontrivial global
idempotents, so `exceptionalCurve_connectedSpace` gives connectedness of E.
If E were a singleton, a trivializing open of its actual degree-one line would
be all of E. Its global sections would then have dimension one. The
original θ₁ contradicts the cotangent-space bound. This argument does not
assume that E is reduced or select a coefficient-field section in A.

A closed point with zero-dimensional stalk is isolated on a Noetherian scheme.
The proof here removes the finite union of all irreducible components other
than that singleton; the zero coheight excludes any different generization.
Connectedness and the preceding θ₁ contradiction exclude such points on E.

The actual Cartier ideal-module stalk is the actual closed-immersion stalk-map
kernel. Its rank-one frame gives a regular principal generator. The original
surjective stalk map therefore satisfies the nonzerodivisor quotient dimension
inequality. The ordinary ambient dimension bound is transported from the
proved normalized chart bound through the original normalization isomorphism.
Together these facts prove `exceptionalCurve_closedPoint_stalk_dimension`:
every closed e of E has dim O_(X,i(e))=2. This conclusion is derived from the
actual fibre; it is not inferred from global dimension two alone.

Finally, the same prescribed Cartier generator extends to a maximal-primary
parameter pair in the actual normal local surface ring. The public
height-one-prime criterion makes the second parameter regular modulo the
first. The original quotient equivalence transports it to O_(E,e), and mapping
the actual radical equality proves that its principal ideal is maximal-primary.
`exceptionalCurve_closedPoint_regularParameter` keeps its ambient lift and
stalk-map value. `exceptionalCurve_closedPoint_cmParameter` is the direct input
for the nonreduced CM-curve consumer.

The geometric basis is the full exceptional-fibre argument of
[Stacks 54.9.5](https://stacks.math.columbia.edu/tag/0B63), with the original
section maps already supplied by [Powers](Powers.lean). The topology argument
uses finite irreducible components and actual stalk coheight. The Cartier
quotient uses the native nonzerodivisor dimension inequality and the public
normal local parameter-pair theorem.

This leaf supplies actual geometry for canonical restriction. It does not
prove a Gorenstein implication, triviality of the surface canonical module,
degree two, a Hilbert function, or rational-double-point classification.
Later canonical generation and slope-two consequences must retain the
nonregularity or genuinely derived degree-at-least-two condition: the blowup
of a regular local surface has E=P¹ and positive line O(1), of degree one.
The genuine degree and Euler-characteristic theory for possibly nonreduced
curves remains a separate downstream obligation.
