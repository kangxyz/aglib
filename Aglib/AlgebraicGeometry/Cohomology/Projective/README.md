# Projective cohomology

`Aglib.AlgebraicGeometry.Cohomology.Projective.Comparison` specializes the
canonical affine Cech comparison to the proved standard coordinate cover of
the actual polynomial projective scheme. For every commutative ring `R`,
coordinate type `ι` and quasicoherent module sheaf, its
`projectiveCechCohomologyAddEquiv` identifies positive-degree coordinate Cech
homology with the original additive `Sheaf.H`. The accompanying naturality
theorem preserves the actual coefficient maps.

The comparison needs neither Noetherianity nor finite generation, and does
not restrict the dimension. It is an additive comparison; the structural
ring action is handled by the general scalar family. Its complex is the
existing full-tuple Cech complex, which remains unbounded even for a finite
coordinate cover. The twist computation below uses its original monomial
decomposition. General coherent finiteness on polynomial projective space
and through actual projective embeddings is proved below.
[Proper/Finiteness](../Proper/Finiteness/README.md) supplies the general
proper extension over Noetherian affine bases.

The lower dependencies are the [native projective coordinate geometry](../../ProjectiveSpace/README.md)
and the [general Cech comparison](../Cech/README.md). The immediate consumer
is the projective twist computation. The projective endpoint feeds the
proper proof; [Proper/Field](../Proper/Field/README.md) supplies the retained
field-valued finiteness families.

`Aglib.AlgebraicGeometry.Cohomology.Projective.TwistingCech` consumes the
constructed actual `O(d)` for every integer `d`. Its all-degree
`twistingCechCohomologyLinearEquivAll` is linear over the original coefficient ring, with scalars
defined by the actual projective structure morphism and Gamma-Spec map.
The target remains the original `Sheaf.H`. Degree zero uses the proved
native Cech augmentation, and successors use the original affine comparison.
This supplies the structural-ring comparison used by the actual homology
calculation below.

`Aglib.AlgebraicGeometry.Cohomology.Projective.LocalCoefficients` identifies
actual `O(d)` sections on every nonempty finite coordinate intersection
with the degree-`d` Laurent monomial module, then with finitely supported
coefficient functions on the permitted integer exponents. Its
`twistingSectionsLaurentLinearEquiv` and monomial version are linear for the
actual projective structural-ring action, by the proved constant-restriction
formula. The Laurent coefficient formula is literal.

`Aglib.AlgebraicGeometry.Cohomology.Projective.FrameIndependence` identifies
the actual geometric transition unit with the ratio of native Laurent
coordinate units and retains every integer power. It proves independence
of the displayed frame and compatibility with every original section
restriction map. The restriction of a homogeneous global polynomial
section maps to the original polynomial with its unchanged coefficients.
These statements supply the actual coefficient maps for the full-tuple
Laurent complex and its subsequent monomial decomposition.

`Aglib.AlgebraicGeometry.Cohomology.Projective.LaurentComparison` supplies
the native `twistingCechLaurentIso` from the unchanged full-tuple Cech
complex to the single original Laurent tuple complex. It transports every
categorical tuple intersection and every actual restriction, retaining the
alternating deletion signs. Its `twistingLaurentCohomologyLinearEquiv`
identifies Laurent-complex homology with the original `Sheaf.H` in every
degree, for arbitrary commutative rings and arbitrary coordinate types.
Finite-coordinate hypotheses enter the subsequent weight decomposition,
not this geometric comparison.

`Aglib.AlgebraicGeometry.Cohomology.Projective.Multiplication` retains the
actual polynomial multiplication morphism on the original Cech complex.
After the geometric chain isomorphisms, its `twistingLaurentPolynomialMap`
is literally multiplication by the unchanged polynomial on every tuple
in every cochain degree. Thus the later residue pairing uses the original
geometric coefficient maps, with their exact Laurent product formula.

`Aglib.AlgebraicGeometry.Cohomology.Projective.Naturality` proves that the
all-degree comparison preserves every actual morphism between twists.
In particular, `twistingLaurentCohomologyLinearEquiv_polynomial` identifies
the literal polynomial product on Laurent cohomology with the original
`Sheaf.H.map` of the actual polynomial multiplication morphism. The lower
[structural-ring coefficient naturality](../Cech/Modules/Naturality.lean)
retains the original degree-zero augmentation and chosen positive-degree
resolution comparisons.

`Aglib.AlgebraicGeometry.Cohomology.Projective.TwistCohomology` proves that
the original `Sheaf.H` of `O(d)` is finite and free over every commutative
base ring, in every cohomological degree and for every integer twist.
An explicit labeling `ι ≃ Fin (n+1)` retains arbitrary ring and coordinate
universes; `ULift (Fin (n+1))` gives the dimensional specialization.
Cohomology vanishes outside degrees zero and `n`, and all positive-degree
cohomology vanishes when `d ≥ -n`. The dimension-zero case retains both
possible empty/full negative-support contributions.

`Aglib.AlgebraicGeometry.Cohomology.Projective.Coproduct` gives the native
linear finite-sum comparison for the cohomology of actual finite coproducts
of twists. It sends each original `Sheaf.H.map` of a summand inclusion to
the literal finitely supported single component. The resulting cohomology
modules are finite and free over arbitrary commutative rings in every degree.

`Aglib.AlgebraicGeometry.Cohomology.Projective.Vanishing` applies the native
finite affine-cover theorem to the original coordinate charts. Actual
cohomology vanishes above degree `n` for every quasicoherent module on
projective `n`-space, with no Noetherian or finite-type premise. Together
with the actual finite negative-twist presentations and coherent kernels in
the geometry family, this supplies the cohomological induction for general
coherent finiteness and the Serre-vanishing argument below.

`Aglib.AlgebraicGeometry.Cohomology.Projective.Finiteness` proves
`projectiveCohomology_finite`: for every Noetherian commutative ring `R`,
coordinate labeling `ι ≃ Fin(n+1)`, coherent module `M` on the actual
polynomial projective space, and `q : ℕ`, its original `Sheaf.H` is a finite
`R`-module for the original structural action. The proof uses decreasing
degree induction, the native short exact kernel sequence, and the original
linear connecting map. It includes dimension zero and does not assume
Serre vanishing or a cohomological finiteness family.

`Aglib.AlgebraicGeometry.Cohomology.Projective.ClosedImmersion` proves
`moduleCohomology_finite_of_projectiveEmbedding` for an actual closed
immersion `i : X → ProjectiveSpace R ι`, a coordinate labeling
`ι ≃ Fin(n+1)`, and an exact factorization `i ≫ toSpec = f`. For Noetherian
`R` and coherent `M`, every original cohomology module is finite for the
original structural ring map of `f`. The proof uses actual coherent
pushforward and the native Cech pushforward isomorphism. Its cohomology
equivalence has the existing geometric cohomology map as its literal
forward map; the structural scalar composition identity is explicit.
This is the embedded projective endpoint over an affine Noetherian base.
[Relative projective projections](Projection/README.md) and
[proper coherent higher images](../DirectImage/Proper/README.md) provide
the corresponding locally Noetherian-target results with their precise
geometric hypotheses.

`SerreVanishing` proves `projectiveSerreVanishing` for every actual coherent
module on polynomial projective `n`-space over a Noetherian commutative ring.
There is one natural bound `B` such that the original `Sheaf.H` of the native
tensor twist `O(d) ⊗ M` vanishes for every integer `d ≥ B` and every positive
cohomological degree. The explicit labeling `ι ≃ Fin (n+1)` preserves arbitrary
universes and dimension zero. The proof uses the proved uniform negative-twist
presentations, coherence of their actual kernels, the original exact tensor
functor, and the original long exact cohomology sequence, descending from the
coordinate-cover bound. No assumed Serre vanishing or resolution family occurs.
`twistingTensorCoproductCohomology_subsingleton` retains the sharper bound
`-n ≤ a+dᵢ` for each summand of an original finite twist coproduct.

`GlobalSections` identifies original twist global sections with native Laurent
H0 through the existing actual Cech augmentation and Laurent complex isomorphism.
Its canonical zero-term embedding is literally the original restriction
family in Laurent coordinates. `GlobalSections.Homogeneous` proves that the
existing homogeneous polynomial section has exactly the original polynomial
in each such tuple coordinate. These original-map normalizations precede the
polynomial global-section and twist-Hom duality consumers.

`GlobalSections.Polynomial` proves the original polynomial-section endpoint
for every nonnegative degree over an arbitrary commutative ring. For finite
coordinates and a chosen coordinate, `homogeneousSectionLinearEquiv` is
exactly the existing homogeneous-section map and is bijective. The original
actual `H0` also identifies linearly with the native homogeneous polynomial
module. `polynomialMultiplicationLinearEquiv` identifies that same polynomial
module with all actual morphisms `O(b) → O(m+b)`, for any integer `b`; its
forward map is the existing polynomial multiplication. Dimension zero is
included, and all scalar actions are the original structural actions. The
leaf passed `1792099705457974000-79259`.

[`FiniteModel`](FiniteModel/README.md) constructs an actual bounded
finite-projective complex for coherent coefficients relatively flat over
a Noetherian base, using a given closed projective embedding and its exact
factorization to the base spectrum. Its original map to the unchanged finite
coordinate-cover Cech complex is a quasi-isomorphism and remains one after
every ring base change. The same model computes original `Sheaf.H` of the
ordinary pulled coefficient in every degree, with original structural
scalars, and represents the installed native derived global sections via
the original module-injective augmentation comparison. The exact chain
base-change square retains original integer Cech and truncation maps.
The final source passed `1792099920579572000-82906`; its independent model,
all-base-change, native-derived and original-map consumer passed
`1792100202455424000-88101`, with only the three standard axioms. The native
degreewise cohomology mate identification and actual perfect sheaf-valued
`Rf_*` are now proved in the focused children recorded by the model guide.
These perfect direct-image statements concern coherent relatively flat
coefficients and their ordinary pullbacks.
[Proper/FiniteModel](../Proper/FiniteModel/README.md) proves that same
sheaf-coefficient endpoint for every proper morphism over a Noetherian
affine base. Arbitrary perfect coefficients remain a separate interface.

`Semicontinuity` proves
`upperSemicontinuous_moduleFiberCohomologyDimension_of_projectiveEmbedding`.
For an actual projective embedding over a Noetherian commutative ring and
coherent relatively flat coefficient, every original residue-field fibre
cohomology dimension is upper semicontinuous. The actual finite-projective
model is constructed inside the public theorem. Its residue-field homology
is identified with the ordinary pulled coefficient using the original
structural action; no desired base-change or model-existence family is an
extra premise. The leaf passed `1792101772364170000-16444`; its independent
arbitrary-universe consumer passed `1792101859151326000-18032`, with only
the three standard axioms.

`EulerCharacteristic` proves
`isLocallyConstant_moduleFiberEulerChar_of_projectiveEmbedding` under the
same geometric hypotheses. `moduleFiberEulerChar` is the intrinsic
alternating sum of the original ordinary fibre-cohomology dimensions,
independent of a chosen embedding or complex. Actual model bounds prove
finite support, and `D.moduleFiberEulerChar_eq_homologyEulerChar` identifies
it with the existing native Euler characteristic after every residue-field
extension, including dimension zero. The leaf passed
`1792102151465195000-22103`; its independent arbitrary-universe consumer
passed `1792102216889418000-23286`, with only the three standard axioms.

`RightExact` proves that original top cohomology on projective `n`-space
sends quasicoherent epimorphisms to native module epimorphisms and actual
right-exact quasicoherent short complexes to exact top-cohomology short
complexes. This works over every commutative ring and follows from original
kernel sequences, the native long exact sequence and the proved cover bound.
The [projective duality family](../Duality/Projective/README.md) consumes this
interface and actual bounded-degree two-step presentations to prove coherent
top Serre duality over Noetherian rings, with field perfectness distinguished.

`Grauert/Global` proves the reduced affine geometric criterion for an actual
projective embedding over a Noetherian ring, with coherent relatively flat
coefficient. Local constancy of an original fibre-cohomology dimension gives
finite projective original cohomology and invertibility of the unchanged
original cohomology base-change map after every ring map. No local-ring
assumption is present. The public endpoints construct the universal model
internally; their independent consumer passed `1792106107718572000-93988`,
with only the three standard axioms. `Grauert` retains the stronger freeness
conclusion over a local ring. Reducedness remains explicit in both versions.
The [proper basic-open criterion](../Proper/BaseChangeLocus.lean) also
applies to this projective case, retaining the original residue-map
surjectivity premise and needing no reducedness.

`LocalBaseChange` supplies the complementary criteria allowing nonreduced
Noetherian local bases. Surjectivity of the original residue-field map in
degree `q` gives arbitrary original base change in that degree. Under that
surjectivity in degree `q+1`, freeness of original cohomology in degree
`q+1` is equivalent to original residue-field surjectivity in degree `q`.
In degree zero, original residue-field surjectivity alone gives freeness,
by the actual model's lower bound. The three geometric endpoints construct
the model internally; their independent consumer passed
`1792104773395115000-70510`, with only the three standard axioms.

[Coherent higher Serre duality](../Duality/Projective/Higher.lean) is now proved for every field, arbitrary projective dimension and every complementary pair `i+j=n`. The original Yoneda/residue pairing is perfect, giving both `Extʲ(M,O(-n-1)) ≃ Hⁱ(M)ᵛ` and `Hⁱ(M) ≃ Extʲ(M,O(-n-1))ᵛ`, with exact original coefficient naturality and dimension zero retained. Its [owning guide](../Duality/Projective/README.md) records the actual presentation proof, field hypothesis, map formulas and public verification.

## Hilbert polynomials and regularity

[HilbertPolynomial](HilbertPolynomial/README.md) proves that `m ↦ χ(O(m) ⊗ F)` is
a polynomial function on all integers for every coherent module `F` on polynomial
projective space over a field, and defines its Hilbert polynomial.
[Regularity](Regularity/README.md) defines Castelnuovo–Mumford regularity and
proves the coordinate epimorphism `∐ᵢ O(0) ⊗ F → O(1) ⊗ F` and the commutation of
coordinate multiplications over any base ring. Nitsure's Lemma 2.1, Mumford's
bound and local constancy of the Hilbert polynomial in flat families remain open.

## Relative projective projections

The focused [Projection](Projection/README.md) family proves coherence of
all actual higher direct images under any base change of polynomial
projective-space projection to a locally Noetherian base. It retains the
original right-derived pushforward, actual Cartesian square and structural
ring actions; neither a Noetherian original presentation ring nor relative
flatness of the coefficient is required. For every quasicoherent coefficient
over an arbitrary base, the same family's sharp relative bound proves that
the original higher images vanish above the projective dimension. Its actual
bounded-derived amplitude theorem sends quasicoherent homology in `[l,b]`
to the native interval `[l,b+n]`, without a condition on representative terms.
Over a locally Noetherian base, the original derived image also preserves
the shared coherent-homology property for every cohomologically bounded
object, with that same explicit interval. The
[Products](Products/README.md) consumer now iterates the original native
`finiteProductOver`, with upper bound `b + ∑ i, d i` and the empty product
equal to the actual base identity. Actual base-change and finite-embedding
consumers now preserve the original product projection and displayed
factorization. Finite maps into such products over a Noetherian affine
base have finite unchanged cohomology in every degree. These results
supply the two inputs for the proper-modification support argument in
[Proper/Finiteness](../Proper/Finiteness/README.md), which discharges the
support-induction premise internally.
