# Native Laurent tuple weight decomposition

Import `Aglib.Algebra.Homology.Simplex.Relative.Weights`, or a focused leaf below.
The sole raw model uses the original `MvPolynomial.coordinateGrading` modules
and original `coordinateLaurentDegreeMap` restrictions. The comparison targets
the actual categorical coproduct of Mathlib alternating relative-simplex
complexes. No replacement cohomology or comparison family is assumed.

Ring and vertex universes are independent: `R : Type u`, `ι : Type v`, and
the native modules have carrier universe `max u v`. The raw object and each
single-weight map require only `CommRing R`. The coproduct comparison requires
`Finite ι`, which makes each tuple family finite; the weight set remains infinite.

- [Exchange](Exchange.lean) gives the generic
  `Finsupp.piSubtypeLEquivDFinsupp R P`. For a finite row type `A` and any relation
  `P : A → W → Prop`, it identifies
  `(∀ a, {w // P a w} →₀ M)` with `(Π₀ w, {a // P a w} → M)`.
  Its two application formulas retain the original matrix coefficient. The
  coefficient module is arbitrary over a semiring. The proof composes native
  sigma-Finsupp/Pi, actual sigma reindexing, sigma-Finsupp/DFinsupp, and finite
  fiber Finsupp/function equivalences.
- [Laurent](Laurent.lean) defines `MvPolynomial.coordinateTupleSet a` as the
  actual finite image of a tuple, and
  `coordinateLaurentTupleCochains R d p := ∀ a : Fin (p + 1) → ι, coordinateGrading R (coordinateTupleSet a) d`.
  `coordinateLaurentTupleCosimplicial` uses the original degree restrictions on
  every tuple-position map. `coordinateLaurentTupleComplex` is its native
  alternating coface-map complex, retaining every tuple in every degree.
  `coordinateLaurentTupleComplex_d_apply` gives the literal signed deletion formula.
- [Terms](Terms.lean) uses the unrestricted original weight type
  `coordinateLaurentWeight d := {e : ι →₀ ℤ // e.degree = d}` and the exact
  negative-coordinate set `coordinateNegativeSupport e := {i | e i < 0}`.
  A weight is allowed on a tuple exactly when this set lies in the tuple range.
  `coordinateLaurentTupleCoefficients` is the original graded monomial
  coordinate map, relabeled by those allowed weights.
  `coordinateLaurentTupleWeightsEquiv` applies the proved finite-row interchange
  to give the native dependent finitely supported sum of actual
  `RelativeSimplex.Cochains`. Its two coefficient equations retain the original
  Laurent exponent and coefficient.
- [Maps](Maps.lean) constructs the original single Laurent monomial injection
  for every weight and admissible tuple, with zero on other tuples.
  `coordinateLaurentTupleWeightInjection_naturality` proves compatibility with
  every actual coordinate restriction. These are genuine cosimplicial maps
  and native chain maps `coordinateLaurentWeightComplexMap`.
  `coordinateLaurentTupleWeightsEquiv_injection` identifies the displayed maps
  with native DFinsupp summand inclusions under the exact term exchange.
- [Coproduct](Coproduct.lean) proves that the actual raw cosimplicial and complex
  cofans are colimiting. It uses the native `ModuleCat.coproductCoconeIsColimit`
  and preservation of coproducts by alternating cofaces, verified through
  the native degree evaluations.
  `coordinateLaurentTupleComplexWeightsIso R d` is the actual chain isomorphism
  from the unchanged raw complex to
  `∐ e : coordinateLaurentWeight d, RelativeSimplex.complex R (coordinateNegativeSupport e.val)`.
  `coordinateLaurentWeightComplexMap_weightsIso_hom` normalizes it by the
  original single-monomial chain maps and native `Sigma.ι`.
- [Homology](Homology.lean) applies native exact coproducts to obtain
  `coordinateLaurentTupleHomologyWeightsIso R d n`, from original raw homology
  to the actual coproduct of the original relative-simplex homology objects.
  `coordinateLaurentTupleHomologyWeightsEquiv` expresses the same comparison
  as the native dependent finitely supported sum. The actual homology map of
  a single-monomial insertion becomes the original `Sigma.ι` or literal
  `DFinsupp.single`, respectively. The hypotheses are `Finite ι` and arbitrary
  `CommRing R`, with independent scalar and vertex universes. Native additive-group
  AB4, shrunk to the vertex universe and transported through the original
  module forgetful functor, proves the required exactness.
- [Projection](Projection.lean) defines
  `coordinateLaurentWeightComplexProjection R d e` by the literal original
  coefficient on every supported tuple. It requires no finite-vertex premise.
  The two original coordinate-restriction coefficient equations prove
  compatibility with every tuple-position map, including the zero extension
  on faces missing required negative vertices. Each projection retracts its
  own original monomial chain map and kills every distinct weight chain map.
- [Finite](Finite.lean) identifies the original empty/full weight indices with
  the native nonnegative/negative integer-degree exponent fibers from the
  lower `RingTheory.MvPolynomial.CoordinateExponents` owner. Their union is
  finite in every fixed degree when `ι` is finite. Actual proper-nonempty
  weight homology is zero, so `coordinateLaurentTupleHomologyEndpointEquiv`
  restricts the original dependent sum to those endpoints by its literal
  coefficient restriction. On `Fin (n + 1)`, every original weight homology
  module is finite free. Thus native instances
  `coordinateLaurentTupleHomology_finite` and `_free` prove finite free raw
  homology in every degree, over an arbitrary commutative ring. The theorem
  `coordinateLaurentTupleHomology_isZero_of_ne_endpoints` gives native vanishing
  for `q ≠ 0` and `q ≠ n`.
  `coordinateLaurentTupleHomology_isZero_of_neg_le_degree` proves the sharp
  positive-degree vanishing bound `-(n : ℤ) ≤ d`, including `n = 0`.
- [Endpoints](Endpoints.lean) gives explicit original scalar presentations in
  positive projective dimension. `coordinateLaurentTupleTopWeightsEquiv R n d hn`
  identifies native top homology with the Finsupp module on the original
  all-negative degree fiber. `coordinateLaurentTupleZeroWeightsEquiv` identifies
  native H0 with Finsupp on natural polynomial exponents of integer degree `d`.
  Both retain actual weight homology components followed by the original
  increasing-tuple or vertex scalar comparison. They retain `hn : n ≠ 0`;
  the full weight sum remains the correct degree-zero interface for `n = 0`.
- [ProjectionHomology](ProjectionHomology.lean) proves that each component of
  the existing homology decomposition is the actual homology map of the
  literal original coefficient chain projection. This uses native summand
  generators and the proved monomial-map retractions and cross-zero equations.
- [FiniteCoordinates](FiniteCoordinates.lean) supplies the geometric universe
  interface. For `R, ι : Type u` and an enumeration `e : ι ≃ Fin (n + 1)`,
  the `_of_equivFin` theorems prove native original homology finite and free
  in every degree, zero outside degrees zero and `n`, and zero in every
  positive degree when `-(n : ℤ) ≤ d`. Finiteness of `ι` follows from the
  enumeration; no additional finite-type instance or equality of a large
  coordinate type with the small `Fin` type is assumed. The actual full-support
  comparison uses the lower native small-target complex reindexing iso.
- [Trace](Trace.lean) defines `coordinateLaurentWeightTrace R n e d w hw` as
  the actual homology map of the original coefficient projection followed by
  the native full-support scalar comparison. It allows projective dimension
  zero and any geometric scalar universe. Its `_homologyπ` formula is exactly
  the original Laurent coefficient of `w` in the native cycle evaluated at
  the enumeration `e.symm`, with its unchanged quotient and positive sign.
  Its `_eq_component` formula identifies the same map with the original
  weight homology component. No replacement trace or assumed comparison is used.

Every weight is retained. Empty negative support contributes degree-zero
cohomology and is handled separately from the proper-nonempty contraction.
For `ι = Fin 1`, all-negative full support also has top degree zero; an
eventual polynomial-only global H0 formula in arbitrary integer degree must
therefore retain a positive-projective-dimension or nonnegative-degree condition.

The supportwise homology calculations use the separate native relative-simplex
contraction, empty-support augmentation, finite full-support calculation and
increasing-tuple trace. The projective Laurent comparison consumes this sole
raw object and identifies its actual homology with unchanged geometric
`Sheaf.H`. Its geometric finite-free endpoints consume the proved finite
surviving-weight calculation. No generic ordered-Cech comparison, bounded
replacement, or proper-base-change endpoint is asserted here.

Each leaf was compiled independently through the shared serialized wrapper:

| Leaf | Successful receipt |
| --- | --- |
| Exchange | `1792081407461561000-59074` |
| Laurent | `1792081711077636000-62758` |
| Terms | `1792082104820373000-67151` |
| Maps | `1792082451117295000-71812` |
| Coproduct | `1792082772067821000-74890` |
| Homology | `1792084486449795000-186` |
| Projection | `1792084645161699000-3405` |
| Finite, sharp degree bound and precise imports | `1792086170181329000-23448` |
| Endpoints | `1792085685795480000-19702` |
| ProjectionHomology | `1792085868223428000-21233` |
| FiniteCoordinates | `1792086313868052000-24663` |
| Trace | `1792086626568368000-26756` |
| Family entry | `1792086746024525000-27755` |

The external task consumer `work/proper-validation/LaurentWeightsConsumer.lean`
passed with receipt `1792083080570427000-77462`. It checks independent ring and
vertex universes, the actual complex coproduct, native `Sigma.ι` normalization,
unchanged monomial coefficients, all tuple-position maps, and the literal signed
differential without a finite-vertex premise for the raw object. The inspected
exchange, term equivalence, complex isomorphism and summand normalization use
only `propext`, `Classical.choice`, and `Quot.sound`.

The external task consumer `work/proper-validation/LaurentWeightHomologyConsumer.lean`
passed with receipt `1792085439655842000-17377`. It checks original homology
decomposition in independent universes, no-finiteness coefficient projections
and their retractions, finiteness of the surviving original index type, native
finite/free instances in all degrees including projective dimension zero, and
vanishing away from the two endpoints. The inspected homology, projection,
finite/free, vanishing, subtype-restriction and nonnegative-exponent comparisons
use only the same three standard axioms.

The arbitrary geometric-coordinate and scalar-universe probe
`work/proper-validation/LaurentFiniteCoordinatesConsumer.lean` passed with
receipt `1792086456883181000-25586`. It checks the native cross-universe
reindexing iso, full-support top comparison, raw finite/free and both vanishing
criteria, including `ULift.{u} (Fin (n + 1))` over an arbitrary `R : Type u`.
It also audits the native projection/homology identity and the explicit Fin
endpoint equivalences. All inspected declarations use only the three standard axioms.
The same consumer was extended to check the exact original-coefficient trace
formula and finite-enumeration cycles normalization; its refreshed successful
receipt is `1792086784553970000-28246`, with the same standard axioms.

[ResidueTrace](ResidueTrace.lean) proves bijectivity of that same original
coefficient trace in residue degree `-card ι`. The actual weight
`coordinateResidueWeight` has every coordinate equal to `-1`; the native
negative-exponent complement shows that it is the only full-support weight
in that degree. Nonnegative weights are impossible when a vertex exists,
and every other weight has zero native homology. Thus
`coordinateLaurentResidueTraceEquiv R n e` identifies the original raw top
homology with `R` for any geometric-universe labeling `e : ι ≃ Fin (n+1)`,
including dimension zero, and its forward map is definitionally the existing
literal coefficient trace. The leaf passed receipt
`1792097605655139000-37695`.

[NegativeTop](NegativeTop.lean) gives the dimension-zero-safe top calculation
for any negative integer degree. Nonnegative weights are impossible in that
degree, so only full negative support contributes. The original raw top
homology identifies with the native scalar Finsupp on the actual all-negative
exponent fiber. Each coefficient is exactly the existing weight trace, and
its cycles formula is the original Laurent coefficient on the enumeration.
The theorem permits arbitrary common ring/coordinate universes and every
`e : ι ≃ Fin (n+1)` without a positive-dimension assumption. The leaf passed
`1792098163606118000-50392`.

[NonnegativeZero](NonnegativeZero.lean) gives the complementary degree-zero
calculation for natural twist degree. The original weight decomposition
restricts to empty negative support; every other weight has zero homology.
Its scalar Finsupp index is the original natural polynomial exponent fiber,
and its cycle coefficients are the original Laurent coefficients on the
chosen one-vertex tuple. The vertex is explicit, ring and coordinate universes
are independent, and dimension zero is included. The leaf passed
`1792098890450562000-64172`.

`NegativeTop.coordinateLaurentTupleHomology_isZero_of_neg_degree_of_ne_top` also proves that original Laurent homology in negative total degree vanishes in every degree distinct from the dimension. The empty-support weights are impossible in negative total degree, so this covers degree zero as well and retains the nonzero top degree when the dimension is zero.
