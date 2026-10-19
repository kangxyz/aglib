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

`VanishingProjective` treats a coherent coefficient `M`, relatively flat over a Noetherian ring
`R`, on a closed subscheme `X` of `P^n_R`, with vanishing positive cohomology. For every ring map
`σ : R →+* B` the base-change map `B ⊗_R H^q(X, M) ⟶ H^q(X_B, M_B)` is an isomorphism in every
degree (`moduleCohomologyBaseChangeMap_isIso_of_vanishing_of_projectiveEmbedding`). `H^0` is
projective (`moduleCohomology_zero_projective_of_vanishing_of_projectiveEmbedding`), and
positive-degree cohomology vanishes after every base change
(`subsingleton_moduleCohomology_pullback_of_vanishing_of_projectiveEmbedding`). The algebra is
`Algebra/Homology/CochainComplex/ProjectiveCokernel`, applied to the finite-projective model.
`VanishingBaseChange` is the local form: over a Noetherian local ring the residue-field maps are
surjective in every degree, and `H^0` is free.

`FlatTwist` applies both to `F(d)`, for `d` at least the Serre bound of a coherent, relatively
flat `F` on `P^n_R` (`exists_twist_baseChange_isIso_and_projective_of_relativeFlat`,
`…_and_free_of_relativeFlat`, `exists_twist_subsingleton_cohomology_pullback_of_relativeFlat`).
This is the exercise after Nitsure's Lemma 3.2 (arXiv:math/0504590v1, p. 15). It also gives
statements (B) and (C) of the proof of Theorem 4.3 for a flat family: the input applied to each
flat `F_{V_i}` in Nitsure's proof, p. 21, over an affine Noetherian base. Nitsure's (B) and (C)
for a non-flat `F` are not proved. The relative flatness of the twists is
`ProjectiveSpace.twistingTensor_relativeFlat`.

`FlatOfSections` proves Nitsure's Lemma 3.2 (p. 15) over an affine base. Let `R` be any
commutative ring and `F` a quasicoherent module on `P^n_R` with finitely many coordinates. If
`H^0(P^n_R, O(d) ⊗ F)` is flat (or projective) over `R` for every `d ≥ N`, then `F` is
relatively flat over `Spec R` (`relativeFlat_of_flat_twistedSections`,
`relativeFlat_of_projective_twistedSections`). Morphisms `O(-d) ⟶ F` are identified linearly
with `H^0(O(d) ⊗ F)` (`negativeTwistHomLinearEquivH0`, through
`ProjectiveSpace.negativeTwistHomLinearEquivSections`). The chart colimit of
`ProjectiveSpace.SectionExtension.Colimit` lifts every finite relation among chart sections to
one flat `Hom(O(-d), F)`. The equational criterion `Module.Flat.of_forall_exists_lift_relation`
(`RingTheory/Flat/EquationalCriterion`) then makes the chart sections flat
(`flat_coordinateOpen_sections_of_flat_negativeTwistHom`). With `FlatTwist`,
`relativeFlat_iff_exists_projective_twistedSections` states Lemma 3.2 as an equivalence for
coherent `F` over a Noetherian ring. A non-affine base needs the gluing G0.

[LargeTwistBaseChange](LargeTwistBaseChange.lean) proves Nitsure's Lemma 3.1 (p. 13) over affine
Noetherian `S = Spec A`, `T = Spec B`. `exists_twist_baseChange_isIso_of_isNoetherianRing`: for
`F` coherent on `P^n_A` and `σ : A →+* B` with `B` Noetherian, there is `N` such that for
`d ≥ N` the positive cohomology of `F(d)` vanishes, on `P^n_A` and on
`P^n_A ×_{Spec A} Spec B`, and `moduleCohomologyBaseChangeMap (toSpec A ι) σ (F(d)) 0` is an
isomorphism. No flatness is assumed, and `N` depends on `σ`.
`exists_twist_baseChange_bijective_projectiveSpace` has target `H^0(P^n_B, 𝒪_B(d) ⊗ π^* F)`,
reached through `baseChangeTwistCohomologyHom`; its composite is not identified with the
canonical mate. The inputs are right exactness of `H^0` of large twists
(`exists_twist_H0_exact_of_exact`, by Serre vanishing for two kernels), `FlatTwist` for sums of
twists (`ProjectiveSpace.twistingCoproduct_relativeFlat`), the naturality
`moduleCohomologyBaseChangeMap_naturality` and
`ProjectiveSpace.twistingTensorPullbackIso_hom_naturality`, and Mathlib's five lemma
(`baseChangeMap_twist_isIso_of_exact`). The bound cannot be uniform in `B`, and `B` cannot be an
arbitrary ring; the module docstring gives the blow-up counterexamples, which are not
formalized.

[BaseChangeTwistLinear](BaseChangeTwistLinear.lean) upgrades the transport
`baseChangeTwistCohomologyHom` to a `B`-linear equivalence `baseChangeTwistCohomologyLinearEquiv`,
for the action of `B` through `P^n_A ×_{Spec A} Spec B ⟶ Spec B` on the source and through
`toSpec B ι` on the target. Its underlying map agrees pointwise with
`baseChangeTwistCohomologyHom`, through `moduleCohomologyPullbackLinearOfEq_apply`; the two
structural ring maps agree by `ProjectiveSpace.baseChangeIso_hom_appTop_comp`
([ProjectiveSpace/BaseChange/ToSpec](../../ProjectiveSpace/BaseChange/ToSpec.lean)).

[FiberBaseChange](FiberBaseChange.lean) proves Nitsure's (B) and (C) (arXiv:math/0504590v1, proof
of Thm 4.3, p. 21) for a coherent `F` on `P^n_A` over a Noetherian ring, flat or not. Beyond one
bound, the positive cohomology of `F(m)` and of all its fibres vanishes, and every fibre map
`κ(s) ⊗ H^0(F(m)) → H^0(P^n_s, F_s(m))` is an isomorphism
(`exists_twist_vanishing_and_fiber_baseChange_isIso`; on `P^n_{κ(s)}`:
`exists_twist_fiber_vanishing_and_bijective_projectiveSpace`). Noetherian induction on `Spec A`
(`TopologicalSpace.NoetherianSpace.exists_forall_le_of_isIrreducible`) with generic flatness
replaces Nitsure's stratification; on each flat piece, Lemma 3.1 and `VanishingProjective` are
composed by `moduleCohomologyBaseChangeMap_isIso_comp` (`BaseChange/Modules/Transitivity`). Only
finitely many bounds of Lemma 3.1 enter, never one uniform in infinitely many `σ`.

[BaseChangeComparison](BaseChangeComparison.lean) proves the comparison that the converse half of
the universal property of the flattening stratification needs (Nitsure, Thm 4.3 (ii), proof
pp. 22–23), over affine Noetherian `S = Spec A`, `T = Spec B`. For `G` coherent on `P^n_A` and
`σ : A →+* B`, assume that at every point `s = σ⁻¹ t` the fibre map
`κ(s) ⊗_A H^0(P^n_A, G) ⟶ H^0(X_s, G_s)` is an isomorphism and `H^q(X_s, G_s) = 0` for `q ≥ 1`,
and that `G_B` is flat over `B`. Then `B ⊗_A H^0(P^n_A, G) ⟶ H^0(X_B, G_B)` is an isomorphism
with projective target (`moduleCohomologyBaseChangeMap_isIso_and_projective_of_fiberwise`).
`moduleCohomologyBaseChangeMap_twist_isIso_and_projective_of_fiberwise` takes `G = F(m)` with
`F_B` flat on `P^n_B`, and `bijective_baseChangeTwist_and_projective_of_fiberwise_projectiveSpace`
writes the fibres and the target on `P^n_{κ(s)}` and `P^n_B`. The inputs are flat base change
through the residue square (`BaseChange/Modules/Composite`), vanishing from the fibres
(`Proper/FiberVanishing`), `VanishingProjective` on `X_B ≅ P^n_B`, and the Nakayama step
`LinearMap.bijective_of_residueField_baseChange_bijective`
([RingTheory/Spectrum/Prime/Bijectivity](../../../RingTheory/Spectrum/Prime/Bijectivity.lean)).
The hypotheses are used only at the points `σ⁻¹ t`, and (B) in every degree `q ≥ 1`.

[Coherent higher Serre duality](../Duality/Projective/Higher.lean) is now proved for every field, arbitrary projective dimension and every complementary pair `i+j=n`. The original Yoneda/residue pairing is perfect, giving both `Extʲ(M,O(-n-1)) ≃ Hⁱ(M)ᵛ` and `Hⁱ(M) ≃ Extʲ(M,O(-n-1))ᵛ`, with exact original coefficient naturality and dimension zero retained. Its [owning guide](../Duality/Projective/README.md) records the actual presentation proof, field hypothesis, map formulas and public verification.

## Hilbert polynomials and regularity

[HilbertPolynomial](HilbertPolynomial/README.md) proves that `m ↦ χ(O(m) ⊗ F)` is
a polynomial function on all integers for every coherent module `F` on polynomial
projective space over a field, defines its Hilbert polynomial, and writes the Hilbert function
as `Σ_{i ≤ n} aᵢ C(m, i)` with integers `aᵢ`.
[Regularity](Regularity/README.md) defines Castelnuovo–Mumford regularity and
proves Nitsure's Lemma 2.1 over any base ring. Its `Mumford/` family proves Mumford's
bound (Nitsure, Thm 2.3) over every field: a coherent submodule of `O^p` on `P^n_k` is
regular at an integer polynomial in its Hilbert coefficients that depends only on `n`
and `p`. Over an affine Noetherian base the fibre Hilbert polynomials are locally constant in
flat families and take finitely many values (`HilbertPolynomial/FlatFamily`, `Finiteness`); they
have degree `≤ n` (`HilbertPolynomial/NatDegree`) and are determined by `n + 1` consecutive values
(`injOn_eval_projectiveHilbertPolynomial_fiber`, in `Finiteness`).

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
